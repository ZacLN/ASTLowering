using Test, Lowering

@testset "pass 1" begin
@testset ":function " begin
Lowering.expand_forms(:(function f end))
Lowering.expand_forms(:(function f(x) end))
Lowering.expand_forms(:(function f(x) end))
Lowering.expand_forms(:(function f(x = 1) end))
Lowering.expand_forms(:(function f(;x = 1) end))
end
@testset ":->" begin
Lowering.expand_forms(:(a -> a))
end
@testset ":let" begin
Lowering.expand_forms(:(let x = 1; end))
end
@testset ":try" begin
Lowering.expand_forms(:(try blk catch end))
Lowering.expand_forms(:(try blk catch e end))
Lowering.expand_forms(:(try blk catch e eblk end))
Lowering.expand_forms(:(try blk catch e eblk finally fblk end))
end
@testset ":lambda" begin

end
@testset ":block" begin
Lowering.expand_forms(:(begin x = 1; y = 2 end))
end
# @testset ":unionall" begin
# end
@testset ":for" begin
Lowering.expand_forms(:(for i = 1:10 end))
end
end