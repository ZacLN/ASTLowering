module Lowering

# currently matching commit 0f8eaa66ee04ae4198a8dab78976a0875853d83f

## Some global stuff

UNUSED = :var"#unused#"
const ssa_counter = [1]
const gensy_counter = [1]
const gensyms = []
const current_gensyms = []
const _current_julia_module_counter = [1]
current_julia_module_counter() = _current_julia_module_counter[1]

include("utils.jl")
include("expansion/methods.jl")
include("expansion/types.jl")
include("expansion/operators.jl")
include("expansion/expansions.jl")

include("resolvescopes.jl")

include("analyzevars.jl") 

include("closures.jl")

# resets ssacounter
function lower(ex)
    reset_ssa_counter()
    expand_forms(ex)
end


function julia_expand1(ex, file, line)
    ex = resolve_scopes(ex)
    ex = analyze_variables(ex)
    ex = closure_convert(ex)
    ex = linearize(ex)
    compact_and_renumber(ex)
end

function julia_expand0(ex, file, line)
    # global current_desugar_loc = Expr(:line, line, file)
    try
        expand_forms(ex)
    catch e
        rethrow(e)
    end
end

function julia_expand(ex, file = :none, line = 0)
    ex = try
        expand_forms(ex)
    catch e
        rethrow(e)
    end
    ex = resolve_scopes(ex)
    ex = analyze_variables!(ex)
    # ex = closure_convert(ex)
    # ex = linearize(ex)
    # ex = compact_and_renumber(ex)
    ex
end

function Base.show_unquoted_expr_fallback(io::IO, ex::Expr, indent::Int, quote_level::Int)
    if ex.head == :method
        print(io, "Method(")
        for i = 1:length(ex.args)
            show(io, ex.args[i])
            i < length(ex.args) && print(io, ", ")
        end
        print(io, ")")
        return
    elseif ex.head in (:core, :top)
        print(io, "$(ex.head).$(ex.args[1])")
        return
    elseif ex.head == :var"local-def"
        print(io, "local-def $(ex.args[1])")
        return
    elseif ex.head in (:inert, :unnecessary, :outerref, :isdefined)
        print(io, "$(ex.head)(", ex.args[1], ")")
        return
    elseif ex.head === :ssavalue
        print(io, "%", Int(ex.args[1]))
        return
    elseif ex.head == :lambda
        print(io, "λ(")
        for i = 1:length(ex.args)
            show(io, ex.args[i])
            i < length(ex.args) && print(io, ", ")
        end
        print(io, ")")
        return
        return
    end
    print(io, "\$(Expr(")
    show(io, ex.head)
    for arg in ex.args
        print(io, ", ")
        show(io, arg)
    end
    print(io, "))")
end

end