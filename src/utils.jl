# helpers
call(args...) = Expr(:call, args...)
core(arg) = Expr(:core, arg)
inert(arg) = Expr(:inert, arg)
meta(args...) = Expr(:meta, args...)
outerref(arg) = Expr(:outerref, arg)
top(arg::Symbol) = Expr(:top, arg)
isexpr(x::Expr, head) = x.head === :head
isexpr(x, head) = false


isssavalue(e) = e isa Expr && e.head === :ssavalue
issymbol(x) = x isa Symbol
issymbol_like(e) = issymbol(e) || isssavalue(e)
isinteger(x::Int) = true
isinteger(x) = false
ispair(x) = x isa Expr || x isa QuoteNode
iskwarg(x) = x isa Expr && x.head === :kw

issimple_atom(x::T) where {T<:Union{Number,Char,String,Nothing,Bool}} = true
issimple_atom(x::Expr) = x.head in (:ssavalue, :thismodule) 
issimple_atom(x) = false

function isdotop(x) 
    x isa Symbol || return false
    str = String(x)
    length(str) == 1 && str[1] == '.' && Base.isoperator(Symbol(str[2]))
end

function check_dotop(e)
    if isdotop_named(e)
        error("invalid function name \"$(deparse(e))\"")
    else
        if e isa Expr
            if e.head === :.
                check_dotop(e.args[2])
            else
                if isquoted(e)
                    check_dotop(e.args[1])
                end
            end
        end
    end
    e
end

iscurly(x) = x isa Expr && x.head === :curly
isvararg(x) = x isa Expr && x.head === :...
isvarargexpr(x) = x isa Expr && x.head === :(::) && isvararg_type_expr(x.args[2])
isvararg_type_expr(x) = x === :Vararg || 
    (x isa Expr && length(x.args) > 0 && ((x.head === :curly && isvararg_type_expr(x.args[1])) || (x.head === :where && isvararg_type_expr(x.args[1]))))

isquoted(x) = x isa Expr && x.head in (:quote, :top, :core, :globalref, :outerref, :line, :break, :inert, :meta, :inbounds, :loopinfo)

issym_dot(e) = e isa Expr && length(e.args) == 2 && e.head == :. && issymbol_like(e.args[1])

iseffect_free(e) = !(e isa Expr) || isssavalue(e) || issym_dot(e) || isquoted(e) || e.head in (:null, :true, :false) || e isa Bool || e isa Nothing

isunderscore_symbol(e) = issymbol(e) && all(==('_'), String(e))

isglobalref(e) = e isa Expr && e.head === :globalref
isouterref(e) = e isa Expr && e.head === :outerref
isouter(x) = x isa Expr && x.head == :outer

isgenerated_meta(e) = length(e.args) == 2 && e.head === :meta && e.args[1] === :generated
isgenerated_only_meta(e) = length(e.args) == 1 && e.head === :meta && e.args[1] === :generated_only

islinenum(x) = x isa Expr && x.head === :line

isdecl(x) = x isa Expr && x.head === :(::)
make_decl(n, t) = Expr(:(::), n, t)
isassignment(x) = x isa Expr && x.head == :(=)
assignment_like(x) = x isa Expr && Base.operator_precedence(x.head) == 1
make_assignment(l, r) = Expr(:(=), l, r)
local_def(x) = Expr(:var"local-def", x)
scope_block(args...) = Expr(:var"scope-block", args...)
block(args...) = Expr(:block, args...)
blockify(e) = e isa Expr && e.head == :block ? (isempty(e.args) ? block(nothing) : e) : block(e)
quotify(e) = Expr(:quote, e)

undot_name(e) = e isa Expr && e.head == :. ? e.args[2].args[1] : e
isdotop_named(e) = isdotop(identifier_name(e))

function identifier_name(e)
    if issymbol(e)
        e
    elseif isglobalref(e)
        e.args[2]
    else
        e
    end
end

function arg_name(v)
    if issymbol(v) && isvalid_name(v)
        v
    elseif !(v isa Expr)
        bad_formal_argument(v)
    else
        if v.head === :... || v.head === :kw
            arg_name(v.args[1])
            decl_var(v.args[1])
        elseif v.head === :(::)
            !issymbol(v.args[1]) && bad_formal_argument(v.args[1])
            decl_var(v)
        elseif v.head === :meta
            if isnospecialize_meta(v, true)
                arg_name(v.args[2])
            else
                bad_formal_argument(v)
            end
        else
            bad_formal_argument(v)
        end
    end
end

function arg_type(v)
    if issymbol(v)
        core(:Any)
    elseif !(v isa Expr)
        bad_formal_argument(v)
    else
        if v.head === :...
            if length(v.args) == 2
                Expr(:..., decl_type(v.args[1]), v.args[2])
            else
                Expr(:..., decl_type(v.args[1]))
            end
        elseif v.head === :(::)
            !issymbol(v.args[1]) && bad_formal_argument(v.args[1])
            decl_type(v)
        elseif v.head === :meta
            if isnospecialize_meta(v, true)
                arg_type(v.args[2])
            else
                bad_formal_argument(v)
            end
        else
            bad_formal_argument(v)
        end
    end
end
bad_formal_argument(v) = error("$(deparse(v)) is not a valid function argument name")
isvalid_name(s) = !(s in (:ccall, :cglobal))

llist_vars(lst) = map(arg_name, filter(a -> !(a isa Expr && a.head === :parameters), lst))
llist_types(lst) = map(arg_type, lst)

decl_var(v) = isdecl(v) ? v.args[1] : v
decl_type(v) = isdecl(v) ? v.args[2] : core(:Any)

isnospecialize_meta(e, one = false) = e isa Expr && (one ? length(e.args) == 2 : length(e.args) > 1) && e.head === :meta && (e.args[1] === :nospecialize || e.args[1] === :specialize)


# utils
function take_while(f, v::Vector{T}) where T
    out = T[]
    for e in v
        if f(e)
            push!(out, e)
        else
            return out
        end
    end
    out
end

function list_tail(lst, n)
    lst[n:end]
end

function eventually_call(ex)
    ex isa Expr && (ex.head === :call || (ex.head in (:where, :(::)) && eventually_call(ex.args[1])))
end

isfunction_def(e) = e isa Expr && (e.head === :function || e.head == :-> || (e.head === :(=) && length(e.args) == 2 && eventually_call(e.args[1])))

isif_generated(e) = e isa Expr && length(e.args) == 4 && e.head === :if && e.args[1] === Expr(:generated)

has_parameters(x::AbstractArray) = length(x) > 0 && x[1] isa Expr && x[1].head === :parameters

function expr_contains_eq(x, expr)
    x == expr || (expr isa Expr && !isquoted(expr) && any(y -> expr_contains_eq(x, y), expr.args))
end

function expr_contains_p(p, expr, filt = x -> true)
    if filt(expr)
        pexpr = p(expr) 
        pexpr !== false && return pexpr
        if expr isa Expr && !isquoted(expr)
            for arg in expr.args
                parg = expr_contains_p(p, arg, filt)
                parg !== false && return parg
            end
        end
        false
    else
        false
    end
end



function insert_after_meta(body, stmts)
    if isempty(stmts)
        body
    else
        meta = take_while(x -> x isa Expr && x.head in (:line, :meta), body.args)
        Expr(body.head, meta..., stmts..., body.args[length(meta) + 1:end]...)
    end
end

function has_dups(lst)
    !allunique(lst)
end

# function flatten_ex(head, e)
#     if isatom(e)
#         e
#     else
#         args = Any[]
#         for x in e.args
#             x = flatten_ex(head, x)
#             if x isa Expr && x.head === head
#                 for a in x.args
#                     push!(args, a)
#                 end
#             else
#                 push!(args, x)
#             end
#         end
#         Expr(e.head, args...)
#     end
# end

function flatten_ex(head, e)
    if isatom(e)
        e
    else
        # Expr(e.head, vcat(map(x -> isexpr(x, head) ? flatten_ex(head, x).args : x, e.args))...)
        ex = Expr(e.head)
        for x in e.args
            if x isa Expr && x.head == head
                tmp = flatten_ex(head, x)
                for a in tmp.args
                    push!(ex.args, a)
                end
            else
                push!(ex.args, x)
            end
        end
        ex
    end
end

flatten_blocks(e) = flatten_ex(:block, e)

function contains(p, expr)
    p(expr) || (expr isa Expr && any(x -> contains(p, x), expr.args))
end
contains(p, v::Vector) = any(p, v)

# TODO
isatom(x) = !(x isa Expr)

function reset_ssa_counter()
    ssa_counter[1] = 1
end
function make_ssavalue()
    ssa = Expr(:ssavalue, first(ssa_counter))
    global ssa_counter[1] += 1
    ssa
end
anybutlast(f, x) = any(f, view(x, 1:length(x) - 1))

function separate(f, list)
    a,b = [], []
    for l in list
        if f(l)
            push!(a, l)
        else
            push!(b, l)
        end
    end
    a, b
end
deparse(x) = string(x)

function let_binds(e)
    if e.args[1] isa Expr && e.args[1].head == :block
        e.args[1].args
    else
        [e.args[1]]
    end
end

function extract_implicit_whereparams(e)
    newparams, whereparams = [], []
    for i in 2:length(e.args)
        p = e.args[i]
        if p isa Expr && length(p.args) == 1 && (p.head === :<: || p.head === :>:)
            T = gensy()
            push!(newparams, T)
            push!(whereparams, Expr(p.head, T, p.args[1]))
        else
            push!(newparams, p)
        end
    end
    newparams, whereparams
end

function lhs_vars(e)
    if issymbol(e)
        [e]
    elseif isdecl(e)
        [decl_var(e)]
    elseif e isa Expr && e.head === :tuple
        vcat(map(lhs_vars, e.args)...)
    else
        []
    end
end

function tuple_to_assignments(lhss0, x)
    assigned = [a for a in lhss0]
    rhss = x.args
    stmts = []
    after = []
    elts = []
    for i in 1:length(lhss0)
        L = lhss0[i]
        R = rhss[i]
        if issymbol_like(L) && 
            (!(R isa Expr) || isquoted(R) || R === nothing) &&
            !contains(e -> e == L, rhss[i:end]) &&
            !contains(e -> e == R, assigned)
            push!(assigned, L)
            push!(stmts, make_assignment(L, R))
            push!(elts, R)
        elseif isvararg(L)
            if i == length(lhss0)
                temp = make_ssavalue()
                return block(
                    stmts,
                    make_assignment(temp, Expr(:tuple, rhss[i:end]...)),
                    after...,
                    make_assignment(L.args[1], temp),
                    Expr(:unnecessary, Expr(:tuple, elts..., Expr(:..., temp)))
                )
            else
                error("invalid ... on non-final assignment location \"$(L.args[1])\"")
            end
        elseif isvararg(R)
            temp = make_ssavalue()
            return block(
                stmts,
                make_assignment(temp, R.args[1]),
                after,
                make_assignment(Expr(:tuple, lhss0[i:end]...), temp),
                Expr(:unnecessary, Expr(:tuple, elts...), Expr(:..., temp))
            )
        else
            temp = eventually_call(L) ? gensy() : make_ssavalue()
            push!(assigned, L)
            if issymbol(temp)
                push!(stmts, local_def(temp))
            end
            push!(stmts, make_assignment(temp, R))
            push!(after, make_assignment(L, temp))
            push!(elts, temp)
        end
    end

    block(stmts..., after..., Expr(:unnecessary, Expr(:tuple, elts...)))
end


function remove_argument_side_effects(e, tup = false)
    if !(e isa Expr)
        e, []
    else
        a = []
        function arg_to_temp(x)
            if iseffect_free(x)
                x
            elseif x.head === :... || x.head == :&
                Expr(x.head, arg_to_temp(x.args[1]))
            elseif x.head === :kw || (tup && x.head === :(=))
                Expr(x.head, x.args[1], arg_to_temp(x.args[2]))
            elseif x.head === :parameters
                Expr(:parameters, map(arg_to_temp, x.args)...)
            elseif x.head === :tuple
                tmp = remove_argument_side_effects(x, true)
                append!(a, tmp[2])
                tmp[1]
            else
                g = make_ssavalue()
                push!(a, make_assignment(g, x))
                g
            end    
        end
        
        Expr(e.head, map(arg_to_temp, e.args)...), a
    end 
end


isreturn(e) = e isa Expr && e.head === :return

has_return(e) = expr_contains_p(isreturn, e, !isfunction_def)

check_no_return(e) = has_return(e) && error("\"return\" not allowed inside comprehension or generator")

has_break_or_continue(e) = expr_contains_p(x -> x isa Expr && x.head in (:break, :continue), e, x -> !(x isa Expr && x.head in (:for, :while)))


function num_non_varargs(args) 
    n = 0
    for a in args
        if !isvararg(a)
            n += 1
        end
    end
    n
end


function fill_missing_argname(a, unused)
    if ispair(a) && a.head == :(::) && length(a.args) == 1
        pushfirst!(a.args, unused ? UNUSED : gensy())
        a
    else
         a
    end
end

function isnodot_sym_ref(e)
    issymbol(e) ||
    e isa Expr && (
    (length(e.args) == 2 && e.head == :globalref) ||
    (length(e.args) == 1 && e.head == :outerref))
end

isquoted_sym(x) = (x isa QuoteNode && issymbol(x.value)) || (x isa Expr && x.head in (:quote, :inert) && length(x.args) == 1 && issymbol(x.args[1]))

function issym_ref(e)
    isnodot_sym_ref(e) ||
    (length(e.args) == 2 && e.head == :. && 
        (isatom(e.args[1]) || issym_ref(e.args[1])) &&
        ispair(e.args[2]) && e.args[2].head in (:quote, :inert) &&
        issymbol(e.args[2].args[1])
    )
end

function dots_to_vararg(a)
    if !isempty(a) && isvararg(last(a))
        a[end] = Expr(:curly, :Vararg, a[end].args[1])
        a
    else
        a
    end
end

function replace_vars(e, renames)
    if issymbol(e)
        get(renames, e, e)
    elseif !ispair(e) || isquoted(e)
        e
    elseif e.head in (:->, :function, :var"scope-block")
        e
    else
        Expr(e.head, map(x -> replace_vars(x, renames), e.args)...)
    end
end

function tuple_to_arglist(e::Expr)::Vector
    if e isa Expr && e.head === :tuple
        map(eq_to_kw, e.args)
    elseif e isa Expr && e.head === :block
        if isempty(e.args)
            []
        elseif length(e.args) == 1
            [eq_to_kw(first(e.args))]
        elseif length(e.args) == 2
            [Expr(:parameters, eq_to_kw(e.args[2])), eq_to_kw(e.args[1])]
        else
            error("more than one semicolon in argument list")
        end
    else
        [eq_to_kw(e)]
    end
end

function eq_to_kw(e)
    isassignment(e) ? Expr(:kw, e.args[1], e.args[2]) : e
end

function undotop(op)
    if isglobalref(op)
        Expr(:globalref, op.args[1], undotop(op.args[2]))
    else
        str = String(op)
        Symbol(str[2:end])
    end
end


# Expr(:lambda, [], [], body)
lam_args(x) = x.args[1]
lam_argnames(x) = llist_vars(lam_args(x))
lam_vinfo(x) = x.args[2]
lam_body(x) = x.args[3]
lam_sp(x) = lam_vinfo(x)[4]

function expand_args_forms(e::Expr)
    ex = Expr(e.head)
    sizehint!(ex.args, length(e.args))
    for a in e.args
        push!(ex.args, expand_forms(a))
    end
    ex
end



function gensy()
    if isempty(current_gensyms)
        g = Symbol("#s", first(gensy_counter))
        gensy_counter[1] += 1
        push!(gensyms, g)
        g
    else
        g = current_gensyms[end]
        deleteat!(current_gensyms, lastindex(current_gensyms))
        g
    end
end

function named_gensy(name)
    g = Symbol("#", gensy_counter[1], "#", name)
    gensy_counter[1] += 1
    g
end

function reset_gensyms()
    empty!(current_gensyms)
    append!(current_gensyms, gensyms)
end

function find_symbolic_label_defs_refs(e, defs = Set{Symbol}(), refs = Set{Symbol}())
    if !(e isa Expr) || isquoted(e)
    else
        if e.head === :symboliclabel
            push!(defs, e.args[1])
        elseif e.head === :symbolicgoto
            push!(refs, e.args[1])
        else
            for a in e.args
                find_symbolic_label_defs_refs(a, defs, refs)
            end
        end
    end
    defs, refs
end

function has_unmatched_symbolic_goto(e)
    defs, refs = find_symbolic_label_defs_refs(e)
    any(!in(defs), refs)
end

function assigned_name(e)
    if isatom(e) 
        e
    elseif e.head in (:call, :curly, :where) || (e.head === :(::) && eventually_call(e))
        assigned_name(e.args[1])
    else
        e
    end
end

function lhs_decls(e)
    if issymbol(e)
        [e]
    elseif isdecl(e) 
        [e]
    elseif e isa Expr && e.head === :tuple
        vcat(lhs_decls.(e.args)...)
    else
        []
    end
end

function all_decl_vars(e)
    if eventually_call(e)
        e
    elseif isdecl(e)
        decl_var(e)
    elseif e isa Expr && e.head === :tuple
        Expr(:tuple, all_decl_vars.(e.args)...)
    else
        e
    end
end


defined_julia_global(v) = false # todo


function first_non_meta(blk)
    for elt in blk
        if !(elt isa Expr && elt.head === :meta)
            return elt
        end
    end
    false
end