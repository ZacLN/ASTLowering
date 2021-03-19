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
_false = :var"false"
_true = :var"true"

include("utils.jl")
include("expansion/methods.jl")
include("expansion/types.jl")
include("expansion/operators.jl")
include("expansion/expansions.jl")

include("resolvescopes.jl")

include("analyzevars.jl") 

include("closures.jl")

include("linearize.jl")

include("expandmacros.jl")

# resets ssacounter
function lower(ex)
    reset_ssa_counter()
    expand_forms(ex)
end


function julia_expand1(ex, file, line)
    ex = resolve_scopes(ex)
    ex = analyze_variables!(ex)
    # ex = closure_convert(ex)
    ex = linearize(ex)
    # compact_and_renumber(ex)
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
    ex = linearize(ex)
    # ex = compact_and_renumber(ex)
    ex
end

function expand_toplevel_expr__(e, file, line)
    ex0 = julia_expand_macroscope(e)
    if istoplevel_only_expr(ex0)
        ex0
    else
        ex = julia_expand0(ex0, file, line)
        th = julia_expand1(Expr(:lambda, [], [], scope_block(blockify(ex))), file, line)
        if length(th.args[1].args[1].args) == 1 && false
        else
            Expr(:thunk, th)
        end
    end
end

function istoplevel_only_expr(e)
    e isa Expr && (e.head in (:toplevel, :line, :module, :import, :using, :export, :error, :incomplete) || (e.head in (:global, :const) && all(issymbol, e.args)))
end
in_expand = false

function expand_toplevel_expr(e, file, line)
    if isatom(e) || istoplevel_only_expr(e)
        isunderscore_symbol(e) && error("all-underscore identifier used as rvalue")
        e
    else
        last = in_expand
        if !last
            reset_gensyms()
            global in_expand = true
        end
        e = expand_toplevel_expr__(e, file, line)
        global in_expand = last
        e
        
    end
end

function expand_to_thunk_(expr, file, line)
    try
        expand_toplevel_expr(expr, file, line)
    catch e
        e
    end
end

function expand_to_thunk_stmt_(expr, file, line)
    expand_to_thunk_(istoplevel_only_expr(expr) ? expr : block(expr, nothing), file, line)
end

function jl_expand_to_thunk_warn(expr, file, line, stmt)
    if stmt
        expand_to_thunk_stmt_(expr, file, line)
    else
        expand_to_thunk_(expr, file, line)
    end
end

jl_expand_to_thunk(expr, file, line) = expand_to_thunk_(expr, file, line)
jl_expand_to_thunk_stmt(expr, file, line) = expand_to_thunk_stmt_(expr, file, line)
julia_expand_macroscope(expr) = julia_expand_macroscope(expr)

function module_default_defs(e)
    name = e.args[2]
    body = e.args[3]
    loc = !isempty(body.args) && isexpr(first(body.args), :line) ? [first(body.args)] : []
    x = name == :x ? :y : :x
    mex = name == :mapexpr ? :map_expr : :mapexpr
    jl_expand_to_thunk(block(
        make_assignment(call(:eval, x), block(loc..., call(core(:eval), name, x))),
        make_assignment(call(:include, x), block(loc..., call(core(:_call_latest), top(:include), name, x))),
        make_assignment(call(:include, Expr(:(::), mex, top(:Function), x)), block(loc..., call(core(:_call_latest), top(:include), mex, name, x)))
    ), :none, 0)
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
    elseif ex.head in (:var"scope-block", :var"break-block", :var"_do_while")
        Base.show_block(io, ex.head, [], Expr(:block, ex.args...), indent, quote_level)
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