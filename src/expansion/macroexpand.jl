mutable struct mactoctx_stack
    m::Module
    parent
end

function expand_macros(e, inmodule, macroctx_stack, onelevel::Int, world::Int)
    if !(e isa Expr) || e.head in (:inert, :module, :meta)
        return e
    else
        if e.head === :quote && length(e.args) == 1
            e = julia_bq_macro(e)
            expand_macros(e, inmodule, macroctx_stack, onelevel, world)
        # elseif e.head === :hygienicscope && e.args == 2
        #     newctx
        elseif e.head === :macrocall
            newctx = macroctx_stack(inmodule)
            result = invoke_julia_macro(e.args, inmodule, newctx.m, world)
            wrap = nothing
            if result isa Expr && result.head == :escape
                result = result.args[1]
            else
                wrap = Expr(:hygienicscope)
            end
            if !onelevel
                result = expand_macros(result, inmodule, wrap ? newctx : macroctx, onelevel, world)
            end
            if wrap !== nothing
                push!(wrap.args, result)
                push!(wrap.args, newctx.m)
            end
            result
        end
    end
end