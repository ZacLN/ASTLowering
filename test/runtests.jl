include("helpers.jl")

e = CSTParser.remlineinfo!(do_replacementes(:(lhs.field[end] = rhs)))
e1 = Lowering.expand_forms(Lowering.julia_expand_macroscope(e))
e2 = scm_lower(e)
compare_lowered(e1, e2)



test_file("/home/zacnugent/.julia/dev/Lowering/src/expansion/expansions.jl")
e = CSTParser.remlineinfo!((do_replacementes(Meta.parseall(String(read("/home/zacnugent/.julia/dev/LanguageServer/src/requests/textdocument.jl")))))).args[9]


using BenchmarkTools
results = []
b = @benchmarkable lower_toplevel(e)

push!(results, run(b))

@profview for i = 1:100 lower_toplevel(e) end

function expr_splat(head, args...)
    e = Expr(:head)
    for a in args
        for x in a
            push!(e.args, x)
        end
    end
    e
end


@testset "pass 1" begin
@testset ":let" begin
    @test_lowering let; end
    @test_lowering let x ; end
    @test_lowering let x = 1; end
    @test_lowering let x::T = 1; end
    @test_lowering let (x,y) = 1 ; end
    @test_lowering let x = 1, y = 1; end
end

@testset ":let" begin
    @test_lowering begin end
    @test_lowering begin x end
    @test_lowering begin begin x end end
end

@testset ":for" begin
    @test_lowering for i = I end
    @test_lowering for i = I body end
    @test_lowering for i = I, j = J end
    @test_lowering for outer i = I, j = J endjr
end

@testset ":vect" begin
    @test_lowering [a, b]
    # @test_lowering [a, b; c]
    # @test_lowering [a = b]
end

@testset ":hcat" begin
    @test_lowering [a b]
    # @test_lowering [a b = 1]
end

@testset ":vcat" begin
    @test_lowering [a;b]
    # @test_lowering [a;b = 1]
end

@testset ":typed_hcat" begin
    @test_lowering T[a b]
    # @test_lowering T[a b = 1]
end

@testset ":typed_vcat" begin
    @test_lowering T[a; b]
    # @test_lowering T[a; b = 1]
end

@testset ":function " begin
    @test_lowering function f end
    @test_lowering function f() end
    @test_lowering function f(a) end
    @test_lowering function f(a, b) end
    
    @test_lowering function f(a = 1) end
    @test_lowering function f(a, b = 2) end
    @test_lowering function f(a = 1, b = 2) end
    @test_lowering function f(a = 1, b = a) end
    @test_lowering function f(a = 1, b = a, c = b) end
    @test_lowering function f(a = 1, b = a, c = b) end

    @test_lowering function f(;p = 1) end
    @test_lowering function f(a, b = 1;p = 1) end
end


@testset ":->" begin
    @test_lowering a -> a
    @test_lowering (a,b) -> a
    @test_lowering function (a) a end
end


@testset ":try" begin
    @test_lowering try blk catch end
    @test_lowering try blk catch e end:(:)
    @test_lowering try blk catch e eblk end
    @test_lowering try blk catch e eblk finally fblk end
end


@testset ":ref" begin
    @test_lowering a[1]
    @test_lowering a[1,2]
    @test_lowering a[begin]
    @test_lowering a[end]
end


# @testset ":unionall" begin
# end
@testset "misc" begin
    @test_lowering f(:a)

end
end