module Match
const metasymbols = (:_, :...)

# function match_(p, expr, state)
#     if p isa Symbol
#         if p == :_
#             state
#         else
#             capt = get(state, p, nothing)
#             if haskey(state, p)
#                 expr == state[p] && state
#             else
#                 (p, expr), state
#             end
#         end
#     elseif p isa Function
#         p(expr) && state
#     elseif p isa NTuple{Any, N} where N
#         if p[1] == :var"-/"
#             p[2] == expr && state
#         elseif p[1] == :var"-^"
#             !match_(p[2], expr, state) && state
#         elseif p[1] == :var"--"
#             match_(p[3], expr, state) && ((p[2], expr), state)
#         elseif p[1] == :var"-$"
#             match_alt(p[2:end], [], [expr], state, false, 1)
#         elseif p[1] == :var"-s"
#             expr isa Symbol && state
#         else
#             expr isa Expr && p[1] == expr.head && match_seq(p[2:end], expr.args, state, length(expr.args))
#         end
#     else
#         p == expr && state
#     end
# end

# function match_alt(alt, prest, expr, state, var, L)
#     for a in alt
#         subma = match_(a, first(expr), state)

#     end
#     if isempty(alt)
#         false
#     else
#         subma && match_seq(prest, expr[2:end], )
#     end
# end

# function match_star_(p, prest, expr, state, var, min, max, L, sofar)
    
# end

# match_star(p, prest, expr, state, var, min, max, L) = match_star_(p, prest, expr, state, var, min, max, L, [])
    


# function match_seq(p, expr, state, L)
    
# end

# match(p, expr) = match_(p, expr, Dict(:__ => expr))
    
# function apply_patterns(plist, expr)
#     # if plist isa Vector
#     # elseif plist === nothing
#     # else
#     #     enew = first(plist)(expr)
#     #     if enew == false
#     #         apply_patterns()
#     #     else
#     #         enew
#     #     end
#     # end
# end

# function pattern_expand(plist, expr)
#     if !(expr isa Expr) || expr.head in (:quote, :varlist, :inert)
#         expr
#     else
#         enew = apply_patterns(plist, expr)
#         if enew == expr
#             function sub(subex)
#                 if !(subex isa Expr)
#                     subex
#                 else
#                     pattern_expand(plist, subex)
#                 end
#             end
#             if expr.head == :lambda
#                 Expr(:lambda, Expr(expr.args[1].head, map(sub, expr.args[1])), map(sub, expr.args[2:end])...)
#             else
#                 Expr(expr.head, map(sub, expr.args))
#             end
#         else
#             pattern_expand(plist, enew)
#         end
#     end
# end

# function pattern_expand1(plist, expr)
#     if !(expr isa Expr) || expr.head in (:quote, :inert)
#         expr
#     else
#         enew = apply_patterns(plist, expr)
#         if enew == expr
#             expr
#         else
#             pattern_expand(plist, enew)
#         end
#     end
# end

# function pattern_replace(plist, expr)
#     if !(expr isa Expr) || expr.head in (:quote, :inert)
#         expr
#     else
#         enew = apply_patterns(plist, expr)
#         if enew == expr
#             map(subex -> !(subex isa Expr) ? subex : pattern_replace(plist, subex), expr.args)
#         else
#             enew
#         end
#     end
# end

# function to_proper(l)
#     l

# # (define (to-proper l)
# # (cond ((null? l) l)
# #   ((atom? l) (list l))
# #   (else (cons (car l) (to-proper (cdr l))))))

# end

macro pattern_lambda(pat, body)
    quote
        function patargs_(p)
            if p isa Symbol && p !== :_ && p !== :...
                [p]
            elseif p isa Expr
                if p.head == :var"-/"
                    []
                else
                    unique(vcat(map(patargs_, p[2])))
                end
            else
                []
            end
        end
        patargs(p) = [:_; patargs_(p)]
        
        args = patargs($(esc(pat)))
        expander = Expr(:lambda, args, $(esc(body)))
        quote
            function (__ex__)
                plambda_expansion($(esc(pat)), __ex__, $(esc(expander)), args)
            end
        end
    end
end

function plambda_expansion(pat, expr, expander, args)
    m = match(pat, expr)
    if m
        map()
    end
end

end