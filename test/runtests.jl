using StaticJulia
using Base.Test

fcall(a, b) = a + b
function test(a, b)
    c = fcall(a, b)
    c == b
end


mod = llvm_module("Test2")

f = llvm_compile(test, (Int, Int), mod)

@code_llvm test(5, 2)

@test f(5, 2) == test(5, 2)
@test f(0, 5) == test(0, 5)

using BenchmarkTools
b1 = @benchmark f(5, 2)
b2 = @benchmark test(5, 2)
# BenchmarkTools is really cool! :P
x = judge(minimum(b1), minimum(b2))
# We can see, our own compiled function has a 600% regression in minimum runtime.
# This is because we haven't run any optimization passes yet!
# Take a look at both IR's to figure out what got optimized!
