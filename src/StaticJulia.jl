module StaticJulia

# a ver
# Sugar defines a couple of utility functions we can use to work with typed ASTs
using LLVM, Sugar

using Sugar: LazyMethod, returntype, resolve_func, expr_type, getfunction,
    method_nargs, sugared

using LLVM: ref, Builder, Value, LLVMType, API


"""
Translates a julia type to a LLVM inbuild type
"""
julia_type_to_llvm{T}(t::T) = julia_type_to_llvm(T)

function julia_type_to_llvm(t::DataType)
    ref = ccall(:julia_type_to_llvm, LLVM.API.LLVMTypeRef, (Any, Ptr{Cint}), t, C_NULL)
    LLVM.LLVMType(ref)
end

# cannot run this example if we don't use Julia's llvm instance
LLVM.libllvm_exclusive && error("llvm is exclusive")

# just have these global for now!
const jlctx = LLVM.Context(cglobal(:jl_LLVMContext, Void))

immutable IRContext
    method::LazyMethod
    slotmap::Dict
    builder
    llvmfunc
    mod
    context
end

# Wasn't wrapped in LLVM, so I added it here for now!
# zero extend (widen)
zext!(builder::Builder, val::Value, dest_type::LLVMType, name::String="") =
    LLVM.Instruction(API.LLVMBuildZExt(ref(builder), ref(val), ref(dest_type), name))

zext!(builder::Builder, val::Value, dest_type::DataType, name::String="") =
    zext!(builder, val, julia_type_to_llvm(dest_type), name)



"""
Processes individual ast nodes and emits instructions for it
"""
function process_ast!(ctx, node)
    if Base.is_linenumber(node) || isa(node, Void)
        return # ignore
    elseif isa(node, Expr)
        head, args = node.head, node.args
        if head == :block
            for elem in args
                process_ast!(ctx, elem)
            end
            return
        elseif head == :call
            f = resolve_func(ctx.method, args[1])
            func_args = args[2:end]
            arg_types = map(x-> expr_type(ctx.method, x), func_args)

            # recursively process arguments
            llvm_args = map(x-> process_ast!(ctx, x), func_args)

            # Inbuilds:
            if (f == (+)) && length(func_args) == 2 && all(x-> x <: Integer, arg_types)
                return add!(ctx.builder, llvm_args...)
            elseif (f == (+)) && length(func_args) == 2 && all(x-> x <: AbstractFloat, arg_types)
                return fadd!(ctx.builder, func_args...)
            elseif f == (==) && length(func_args) == 2 && all(x-> x <: Integer, arg_types)
                tmp = icmp!(ctx.builder, LLVM.API.LLVMIntEQ, llvm_args...)

                return  zext!(ctx.builder, tmp, Bool)
            else
                # it's not an inbuild, so we need to compile it!
                llvm_fun = compile_llvm_func(f, arg_types, ctx.mod, jlctx)
                return call!(ctx.builder, llvm_fun, llvm_args) # emit call
            end
        elseif head == :unless
            # TODO implement
            error("Unless not implemented")
            #=
                [block1]
                <unless x> <goto 10>
                [block_unless]
                <label 10>
                [block3]
            =#
            condition = args[1]
            condition_llvm = process_ast!(ctx, condition)
            current_block = position(ctx.builder)
            ifblock_expr = args[2]
            elseblock_expr = length(args) == 3 ? args[3] : Expr(:block)
            ifblock = BasicBlock(ctx.llvmfunc, "then", ctx.context)
            continueblock = BasicBlock(ctx.llvmfunc, "continue", ctx.context)
            position!(ctx.builder, ifblock)
            process_ast!(ctx, ifblock_expr)
            position!(ctx.builder, current_block)
            return br!(ctx.builder, condition_llvm, ifblock, elseblock)
        elseif head == :(=)
            lhs, rhs = args
            @assert isa(lhs, Slot) # left hand should always be a slot
            llvm_value = process_ast!(ctx, rhs)
            ctx.slotmap[lhs] = llvm_value # update slot with the correct llvm value
            return llvm_value
        elseif head == :return
            ret_args = if length(args) == 1
                return ret!(ctx.builder, process_ast!(ctx, args[1]))
            elseif isempty(args)
                return #ingore empty return
            end
        end
    elseif isa(node, Slot)
        return ctx.slotmap[node] # get llvm value corresponding to slot
    end
    error("Node: $node not supported")
end

function compile_llvm_func(f::Function, param_types, mod, llvmctx = jlctx)
    # lazy method is a helper type from Sugar, which makes it easier
    # to get an AST and type information from a function
    method = LazyMethod((f, (param_types...)))
    compile_llvm_func(method, param_types, mod, llvmctx)
end

function compile_llvm_func(method::LazyMethod, param_types, mod, llvmctx = jlctx)

    ltypes = julia_type_to_llvm.(param_types)
    # needs to be a vector
    param_types_llvm = [ltypes...]
    println(method.signature)
    return_type = Core.Inference.return_type(method.signature...)
    return_type_llvm = julia_type_to_llvm(return_type)

    fun_type = LLVM.FunctionType(return_type_llvm, param_types_llvm)
    name = string(Symbol(getfunction(method)))
    llvmfun = LLVM.Function(mod, name, fun_type)

    # insert slot mappings for argument slots
    slotmap = Dict{Any, Any}(map(2:method_nargs(method)) do i
        SlotNumber(i) => parameters(llvmfun)[i - 1]
    end)
    # generate IR
    Builder(llvmctx) do builder
        ctx = IRContext(method, slotmap, builder, llvmfun, mod, llvmctx)
        entry = BasicBlock(llvmfun, "entry", llvmctx)
        position!(builder, entry)
        # get the body ast, in a decompiled form (we could also try
        # to directly work with Julia's lowered AST):
        body = sugared(method.signature...)
        process_ast!(ctx, body)
        println(mod)
    end
    verify(llvmfun)
    # optionally add attributes to function
    # push!(function_attributes(llvmfun), EnumAttribute("alwaysinline"))
    llvmfun
end

"""
Generates llvm ir, compiles it and returns it wrapped in a julia function
"""
function llvm_compile(f, param_types, mod)
    llvmfun = compile_llvm_func(f, param_types, mod)
    return_type = Core.Inference.return_type(f, Tuple{param_types...})
    argnames = [:($(Symbol(string("arg", i)))) for i in 1:length(param_types)]
    jlfun = quote
        function $(Symbol(name))($(argnames...))
            Base.llvmcall($(LLVM.ref(llvmfun)), $return_type, Tuple{$(param_types...)}, $(argnames...))
        end
    end
    eval(jlfun)
end

llvm_module(name::String) = LLVM.Module(name, jlctx)

export llvm_compile, llvm_module

end # module
