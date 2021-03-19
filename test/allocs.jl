using Lowering, Profile
include("helpers.jl")
e = CSTParser.remlineinfo!(replace_macrocalls(do_replacementes(Meta.parseall(String(read("/home/zacnugent/.julia/dev/Lowering/src/expansion/expansions.jl"))))))


for i in 1:length(e.args)
    Lowering.expand_forms(Lowering.julia_expand_macroscope(e.args[i]))
end

Profile.clear_malloc_data()

for i in 1:length(e.args)
    Lowering.expand_forms(Lowering.julia_expand_macroscope(e.args[i]))
end
exit()