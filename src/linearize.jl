function linearize(e)
    if !(e isa Expr) || isquoted(e)
        e
    elseif e.head === :lambda
        e.args[3] = compile_body(e.args[3], merge(e.args[2][1], e.args[2][2]), e)
    else
        e1 = Expr(e.head)
        for a in e.args
            push!(e1.args, linearize(a))
        end
        e = e1
    end
    e
end

# this pass behaves like an interpreter on the given code.
# to perform stateful operations, it calls `emit` to record that something
# needs to be done. in value position, it returns an expression computing
# the needed value. in the future, all intermediate values will have
# numbered slots (or be simple immediate values), and then those will be the
# only possible returned values.
function compile_body(e, vi, lam)
    code = [] # statements
    filename = true
    first_line = true
    current_loc = false
    rett = false
    global_const_error = false
    arg_map = false             # map arguments to new names if they are assigned
    label_counter = 0           # counter for generating label addresses
    label_map = Dict()          # maps label names to generated addresses
    label_nesting = Dict()      # exception handler and catch block nesting of each label
    finally_handler = false     # Current finally block info: `(var label map level tokens)` 
                                # `map` is a list of `(tag . action)` which will
                                # be emitted at the exit of the block. Code
                                # should enter the finally block via `enter-finally-block`.
    handler_goto_fixups = []    # `goto`s that might need `leave` exprs added
    handler_level = 0           # exception handler nesting depth
    catch_token_stack = []      # tokens identifying handler enter for current catch blocks
    
    function emit(c)
        push!(code, c)
        c
    end
    
    function make_label()
        label_counter += 1
        label_counter - 1
    end
    
    mark_label(l) = emit(Expr(:label, l))
    
    function make_and_mark_label()
        if !isempty(code) && last(code) isa Expr && last(code).head == :label
            last(code).args[1]
        else
            l = make_label()
            mark_label(l)
            l # todo : is this right?
        end
    end
    
    function enter_finally_block(action, need_goto = true)
        tags = finally_handler[3]
        tag = isempty(tags) ? 1 : first(last(tags)) + 1
        push!(tags, tag)
        emit(make_assignment(first(finally_handler), tag))
        if need_goto
            label = finally_handler[2]
            dest_handler_level = finally_handler[4]
            dest_tokens = finally_handler[5]
            pexc = pop_exc_expr(catch_token_stack, dest_tokens)
            pexc !== false && emit(pexc)
            emit(Expr(:leave, 1 + (handler_level - dest_handler_level)))
            emit(Expr(:goto, label))
        end
        tag
    end

    function pop_exc_expr(src_tokens, dest_tokens)
        if src_tokens == dest_tokens
            false
        else
            for i in 1:length(src_tokens)
                if length(src_tokens) - i == length(dest_tokens) && src_tokens[i + 1:end] == dest_tokens
                    return Expr(:pop_exception, src_tokens[i]) 
                end
            end
            error("Attempt to jump into catch block")
        end
    end

    function emit_return(x)
        function actually_return(x)
            x = if rett
                compile(convert_for_type_decl(x, rett), [], true, false)
            else
                x
            end
            tmp = if (isempty(catch_token_stack) ? isvalid_ir_return : issimple_atom)(x)
                false
            else
                make_ssavalue()
            end
            tmp !== false && emit(make_assignment(tmp, x))
            pexc = pop_exc_expr(catch_token_stack, [])
            pexc !== false && emit(pexc)
            emit(Expr(:return, tmp !== false ? tmp : x))
        end

        if x !== false # todo: is this right?
            if handler_level > 0
                tmp = if issimple_atom(x) && (!isssavalue(x) || finally_handler == false)
                    false
                elseif finally_handler !== false 
                    new_mutable_var()
                else
                    make_ssavalue()
                end
                tmp !== false && emit(make_assignment(tmp, x))
                if finally_handler !== false
                    enter_finally_block(Expr(:return, tmp !== false ? tmp : x))
                else
                    emit(Expr(:leave, handler_level))
                    actually_return(tmp !== false ? tmp : x)
                end
                tmp !== false ? tmp : x
            else
                actually_return(x)
            end
        else
            false # todo : correct?
        end
    end

    function emit_break(labl) # todo : check type?
        lvl = labl.args[2]
        dest_tokens = labl.args[3]
        if finally_handler !== false && finally_handler[4] > lvl
            enter_finally_block(Expr(:break, labl))
        else
            pexc = pop_exc_expr(catch_token_stack, dest_tokens)
            pexc !== nothing && emit(pexc)
            if handler_level > lvl
                emit(Expr(:leave, handler_level - lvl))
            end
            emit(Expr(:goto, labl.args[1]))
        end
    end

    function new_mutable_var(name...)
        g = isempty(name) ? gensy() : named_gensy(first(name))
        push!(lam_vinfo(lam)[1], VarInfo(g, :Any, BitArray((false, true, false, false, false, false, false, false)))) 
        g
    end

    function check_top_level(e)
        function head_to_text(h)
            if h == :abstract_type 
                "\"abstract type\""
            elseif h === :primitive_type
                "\"primitive type\""
            elseif h === :struct_type
                "\"struct\""
            elseif h === :method
                "\"method definition\""
            else
                string("\"$h\"")
            end
        end
        if !isempty(lam.args[2]) # todo: use lam accessor func
            error("$(head_to_text(e.head)) expression not at top level")
        end
    end

    function compile_args(lst, break_labels)
        issimple = all(x -> issimple_atom(x) || issymbol(x) || x isa QuoteNode || (x isa Expr && x.head in (:quote, :inert, :top, :core, :globalref, :outerref, :boundscheck)), lst)

        vals = []
        for arg in lst
            aval = compile(arg, break_labels, true, false)
            aval = aval == false ? nothing : aval
            push!(vals, if !issimple &&
                           !issimple_atom(arg) &&
                           !issimple_atom(aval) &&
                           !(arg isa Expr && arg.head in (:quote, :inert, :top, :core, :globalref, :outerref, :boundscheck)) &&
                           !(issymbol(aval) && aval in lam_args(lam)) &&
                           !(issymbol(arg) && (arg == last(lst) || isempty(vals)))
                tmp = make_ssavalue()
                emit(make_assignment(tmp, aval))
                tmp
            else
                aval
            end)
        end
        vals
    end

    function compile_cond(ex, break_labels)
        cnd = compile(ex, break_labels, true, false)
        cnd = cnd == false ? nothing : cnd
        if !isvalid_ir_argument(cnd)
            tmp = make_ssavalue()
            emit(make_assignment(tmp, cnd))
            tmp
        else
            cnd
        end
    end
    
    function emit_assignment(lhs, rhs)
        if rhs
            if isvalid_ir_value(lhs, rhs)
                emit(make_assignment(lhs, rhs))
            else
                rr = make_ssavalue()
                emit(make_assignment(rr, rhs))
                emit(make_assignment(lhs, rr))
            end
        else
            false
        end
    end

    function compile(e, break_labels, value::Bool, tail::Bool)
        if e isa Nothing || e isa Bool || e isa QuoteNode|| !(e isa Expr) || e.head in (:null, :true, :false, :ssavalue, :quote, :inert, :top, :core, :copyast, :the_expection, :$, :globalref, :outerref, :thismodule, :cdecl, :stdcall, :fastcall, :thiscall, :llvmcall)
            e1 = arg_map isa Dict ? get(arg_map, e, e) : e
            if value && (isunderscore_symbol(e) || (e isa Expr && (e.head == :outerref || e.head == :globalref) && isunderscore_symbol(e.args[1])))
                error("all-underscore identifier used as rvalue $(format_loc(current_loc))")
            end

            if tail
                emit_return(e1)
            elseif value
                e1
            elseif issymbol(e1)
                emit(e1)
                false
            elseif e1 isa Expr && e1.head == :outerref
                emit(e1)
                false
            elseif e1 isa Expr && e1.head == :globalref
                emit(e1)
                false
            else
                false
            end
        else
            if e.head in (:call, :new, :splatnew, :foreigncall, :cfunction, :new_opaque_closure)
                args = if e.head === :foreigncall
                    fptr = e.args[1]
                    vcat(isatom(fptr) || !istuple_call(fptr) ? compile_args([e.args[1]],        break_labels) : [e.args[1]],
                        list_head(e.args[2:end], 4), 
                        compile_args(e.args[5:end], break_labels)
                    )
                elseif e.head === :cfunction
                    fptr = first(compile_args([e.args[2]], break_labels))
                    [e.args[1]; fptr; e.args[3:end]]
                elseif length(e.args) > 1 && e.args[1] === :cglobal || e.args[1] == Expr(:outerref, :cglobal)
                    [e.args[1]; e.args[2]; compile_args(e.args[3:end], break_labels)]
                else
                    compile_args(e.args, break_labels)
                end
                callex = Expr(e.head, args...)

                if tail
                    emit_return(callex)
                elseif value
                    callex
                else
                    emit(callex)
                end
            elseif e.head === :(=)
                lhs = e.args[1]
                if issymbol(lhs) && isunderscore_symbol(lhs)
                    compile(e.args[2], break_labels, value, tail)
                else
                    rhs = compile(e.args[2], break_labels, true, false)
                    lhs = arg_map !== false && issymbol(lhs) ? get(arg_map, lhs, lhs) : lhs
                    if value && rhs
                        rr = isatom(rhs) || isssavalue(rhs) || rhs === nothing ? rhs : make_ssavalue()
                        if rr != rhs
                            emit(make_assignment(rr, rhs))
                        end
                        emit(make_assignment(lhs, rr))
                        tail ? emit_return(rr) : rr
                    else
                        emit_assignment(lhs, rhs)
                    end
                end
            elseif e.head === :block
                last_fname = filename
                fnm = first_non_meta(e.args)
                fname = !isempty(e.args) && islinenum(fnm) && length(fnm.args) > 1 ? fnm.args[2] : filename
                file_diff = fname != last_fname
                need_meta = file_diff && last_fname !== false && e !== lam_body(lam)
                if file_diff
                    filename = fname
                end
                if need_meta
                    emit(meta(:push_loc, fname))
                end
                for i in 1:length(e.args)
                    if i == length(e.args)
                        compile(e.args[i], break_labels, value, tail)
                    else
                        compile(e.args[i], break_labels, false, false)
                    end
                    if need_meta
                        if !tail || (last(code) && last(code).head == :meta) # this is wrong
                            emit(meta(:pop_loc))
                        else
                            retv = pop!(code)
                            if iscomplex_return(retv)
                                tmp = make_ssavalue()
                                emit(make_assignment(tmp, retv.args[1]))
                                emit(meta(:pop_loc))
                                emit(Expr(:return, tmp))
                            else
                                emit(meta(:pop_loc))
                                emit(retv)
                            end
                        end
                    else
                        file_diff && (filename = last_fname)
                    end
                end
            elseif e.head === :return
                compile(e.args[1], break_labels, true, true)
                false
            elseif e.head === :unnecessary
                value ? compile(e.args[1], break_labels, value, tail) : false
            elseif e.head === :if || e.head === :elseif
                cond = e.args[1]
                if isexpr(cond, :block)
                    if length(cond.args) > 1
                        compile(butlast(cond), break_labels, false, false)
                    end
                    cond = last(cond.args)
                end
                tests = map(function (clause)
                    emit(Expr(:gotoifnot, compile_cond(clause, break_labels), :_))
                end, isexpr(cond, :&&) ? cond.args : [cond])
                end_jump = Expr(:goto, :_)
                val = value && !tail ? new_mutable_var() : false
                v1 = compile(e.args[2], break_labels, value, tail)

                if val !== false
                    emit_assignment(val, v1)
                end
                if !tail && (length(e.args) > 2 || val !== false)
                    emit(end_jump)
                end
                elselabel = make_and_mark_label()
                foreach(test -> (test.args[2] = elselabel), tests)
                v2 = length(e.args) > 2 ? compile(e.args[3], break_labels, value, tail) : nothing
                if val !== false
                    emit_assignment(val, v2)
                end
                if !tail
                    end_jump.args[1] = make_and_mark_label()
                elseif length(e.args) == 2
                    emit_return(v2)
                end
                val
            elseif e.head === :_while
                endl = make_label()
                topl = make_and_mark_label()
                test = compile_cond(e.args[1], break_labels)
                emit(Expr(:gotoifnot, test, endl))
                compile(e.args[2], break_labels, false, false)
                emit(Expr(:goto, topl))
                mark_label(endl)
                value ? compile(Expr(:null), break_labels, value, tail) : false
            elseif e.head === :_do_while
                endl = make_label()
                topl = make_and_mark_label()
                compile(e.args[1], break_labels, false, false)
                emit(Expr(:gotoifnot, compile_cond(e.args[2], break_labels), endl))
                emit(Expr(:goto, topl))
                mark_label(endl)
                value ? compile(Expr(:null), break_labels, value, tail) : false
            elseif e.head === :var"break-block"
                endl = make_label()
                compile(e.args[2], merge(break_labels, Dict(e.args[1] => [endl, handler_level, catch_token_stack])), false, false)
                mark_label(endl)
                value && compile(Expr(:null), break_labels, value, tail)
            elseif e.head === :break
                labl = get(break_labels, e.args[1], nothing)
                if labl === nothing
                    error("break or continue outside loop")
                else
                    emit_break(labl)
                end
            elseif e.head === :label || e.head === :symboliclabel
                if e.head === :symboliclabel
                    if haskey(label_nesting, e.args[1])
                        error("label \"$(e.args[1])\" defined multiple times")
                    else
                        label_nesting[e.args[1]] = [handler_level, catch_token_stack]
                    end
                else
                    m = get(label_map, e.args[1], false)
                    if m !== false
                        emit(Expr(:label, m))
                    else
                        label_map[e.args[1]] = make_and_mark_label()
                    end

                    if tail
                        emit_return(Expr(:null))
                    else
                        value && error("misplaced label")
                    end
                end
            elseif e.head === :symbolicgoto
                m = get(label_map, e.args[1], false)
                m = m !== false ? m : let l = make_label()
                    label_map[e.agrs[1]] = l
                    l
                end
                emit(Expr(:null))
                emit(Expr(:goto, m))
                push!(handler_goto_fixups, [code, handler_level, catch_token_stack, e.args[1]])
                false
            elseif e.head === :trycatch || e.head === :tryfinally
                handler_token = make_ssavalue()
                catch_ = make_label()
                endl = make_label()
                last_finally_handler = finally_handler
                finally_ = e.head === :tryfinally ? new_mutable_var() : false
                my_finally_handler = false

                emit(make_assignment(handler_token, Expr(:enter, catch_)))
                handler_level += 1
                if finally_ !== false
                    my_finally_handler = [finally_, endl, [], handler_level, catch_token_stack]
                    finally_handler = my_finally_handler
                    emit(make_assignment(finally_, -1))
                end
                v1 = compile(e.args[1], break_labels, value, false)
                val = value && !tail ? new_mutable_var() : false
                val && v1 && emit_assignment(val, v1)

                if tail
                    v1 && emit_return(v1)
                    !finally_ && (endl = false)
                else
                    emit(Expr(:leave, 1))
                    emit(Expr(:goto, endl))
                end

                handler_level -= 1
                mark_label(catch_)
                emit(Expr(:leave, 1))
                if finally_
                    enter_finally_block(call(top(:rethrow)), false)
                    mark_label(endl)
                    finally_handler(last_finally_handler)
                    compile(e.args[2], break_labels, false, false)
                    for (i,a) in enumerate(my_finally_handler[3])
                        skip = tail && i == length(my_finally_handler[3]) && a[2] == :return ? false : make_label()
                        if skip
                            tmp = make_ssavalue()
                            emit(make_assignment(tmp, call(core(:(===)), finally_, a.head)))
                            emit(Expr(:gotoifnot, tmp, skip))
                        end
                        ac = a[2:end]
                        if ac.head === :return
                            emit_return(ac.args[1])
                        elseif ac.head === :break
                            emit_break(ac.args[1])
                        else
                            emit(ac)
                        end
                        skip && mark_label(skip)
                    end
                else
                    push!(catch_token_stack, handler_token)
                    v2 = compile(e.args[2], break_labels, value, tail)
                    val && emit_assignment(val, v2)
                    !tail && emit((Expr(:pop_exception, handler_token)))
                    endl !== false && mark_label(endl)
                    pop!(catch_token_stack)
                end
                val
            elseif e.head === :newvar
                if !(!isempty(code) && first(code) == e) && e.args[1] in first(lam_vinfo(lam))
                    emit(e)
                else
                    false
                end
            elseif e.head === :global
                value && error("misplaced \"global\" declaration")
                emit(e)
            elseif e.head === :var"local-def"
                false
            elseif e.head === :local
                false
            elseif e.head === :var"moved-local"
                push!(lam_vinfo(lam), (e.args[1], :Any, 2))
                false
            elseif e.head === :const
                if islocal_in(e.args[1], lam)
                    error("unsupported `const` dclaration on local variable $(format_loc(current_loc))")
                else
                    if lam.args[1] isa Expr # todo : what is lam structure
                        if !global_const_error
                            global_const_error =  current_loc
                        end
                    else
                        emit(e)
                    end
                end
            elseif e.head === :isdefined
                tail ? emit_return(e) : e
            elseif e.head === :boundscheck
                tail ? emit_return(e) : e
            elseif e.head === :method
                !isempty(lam.args[1]) && error("Global method definition $(linenode_string(current_loc)) needs to be placed at the top level, or use \"eval\"")

                if length(e.args) > 1
                    sig = compile(e.args[2], break_labels, true, false)
                    sig = isvalid_ir_argument(sig) ? sig : let l = make_ssavalue(); 
                        emit(make_assignment(l, sig))
                        l
                    end
                    lam = e.args[3]
                    lam = lam isa Expr && lam.head == :lambda ? linearize(lam) : let l = make_ssavalue()
                        emit(make_assignment(l, compile(lam, break_labels, true, false)))
                        l                        
                    end

                    emit(Expr(:method, e.args[2] || false, sig, lam))
                    if value
                        compile(Expr(:null), break_labels, value, tail)
                    else
                        false
                    end
                else
                    if tail
                        emit_return(e)
                    elseif value
                        e
                    else
                        emit(e)
                    end
                end
            elseif e.head === :lambda
                temp = linearize(e)
                if tail
                    emit_return(temp)
                elseif value
                    temp
                else
                    emit(temp)
                end
            elseif e.head === :thunk || e.head === :module
                check_top_level(e)
                emit(e)
                tail ? emit_return(Expr(:null)) : Expr(:null)
            elseif e.head === :var"toplevel-only"
                check_top_level(e)
                Expr(:null)
            elseif e.head === :toplevel
                check_top_level(e)
                val = make_ssavalue()
                emit(make_assignment(val, e))
                tail ? emit_return(val) : val
            elseif e.head === :import || e.head === :using || e.head === :export
                check_top_level(e)
                emit(e)
                have_ret = !isempty(code) && first(code) isa Expr && first(code).head === :return
                if tail && !have_ret
                    emit_return(Expr(:null))
                end
                Expr(:null)
            elseif e.head === :gc_preserve_begin
                args = compile_args(e.args, break_labels)
                Expr(e.head, args...)
            elseif e.head in (:line, :meta, :inbounds, :loopinfo, :gc_preserve_end, :aliasscope, :popaliasscope)
                have_ret = !isempty(code) && first(code) isa Expr && first(code).head === :return
                if e.head === :line
                    current_loc = e
                    if first_line
                        first_line = false
                        emit(e)
                    else
                        emit(Expr(:line, e.args[1]))
                    end
                elseif e.head === :meta && length(e.args) > 1 && e.agrs[1] === :var"ret-type"
                    @assert !value || tail
                    @assert !rett
                    rett = e.args[2]
                else
                    emit(e)
                end
                if tail && !have_ret
                    emit_return(Expr(:null))
                end
                Expr(:null)
            elseif e.head in (:(≔), :(⩴), :(≕), :(:=))
                error("unsupported assignment operator \"$(deparse(e.head))\"")
            elseif e.head === :error
                error(e.args[1])
            else
                error("invalid syntax $(deparse(e))")
            end
        end
    end
    for k in (lam_args(lam))
        if asgn(vi[k])
            if arg_map === false
                arg_map = Dict()
            end
            arg_map[vi[k].name] = new_mutable_var(vi[k].name)
        end
    end

    compile(e, [], true, true)

    for x in handler_goto_fixups
        point, hl, src_tokens, lab = x
        target_nesting = get(label_nesting, lab, false)
        !target_nesting && error("label \"$lab\" referenced but not defined")
        target_level = first(target_nesting)
        if target_level > hl
            error("cannot goto label \"$lab\" inside try/catch block")
        elseif target_level == hl
            # remove empty slot
            deleteat!(point, 3)
            error("L4388")
        else
            point[2] = Expr(:leave, hl - target_level)
        end
        pexc = pop_exc_expr(src_tokens, target_nesting[2])
        if pexc !== nothing
            insert!(point, 2, pexc)
        end
    end

    if global_const_error
        error("`global const` declaration not allowed inside function $(format_loc(global_const_error))")
    end

    stmts = code
    di = definitely_initialized_vars(stmts, vi) # todo typeof di?
    body = block(filter(e -> !(e isa Expr && e.head === :newvar && haskey(di, e.args[1])), stmts)...)
    if arg_map !== false
        argmap2 = []
        for (k,v) in arg_map
            push!(argmap2, make_assignment(v, k))
        end
        insert_after_meta(body, argmap2)
        error("L4399")
    else
        body
    end
end

# Find newvar nodes that are unnecessary because (1) the variable is not
# captured, and (2) the variable is assigned before any branches.
# This is used to remove newvar nodes that are not needed for re-initializing
# variables to undefined (see issue #11065).
# It doesn't look for variable *uses*, because any variables used-before-def
# that also pass this test are *always* used undefined, and therefore don't need
# to be *re*-initialized.
# The one exception to that is `@isdefined`, which can observe an undefined
# variable without throwing an error.
function definitely_initialized_vars(stmts, vi)
    vars = Dict()
    di = Dict()
    for e in stmts
        for_each_isdefined(x -> haskey(vars, x) && delete!(vars, x), e)
        if isexpr(e, :newvar)
            vinf = var_info_for(e.args[1], vi)
            if vinf !== false && !capt(vinf)
                vars[e.args[1]] = true
            end
        elseif e isa Expr && (e.head in (:goto, :gotoifnot) || 
                (e.head == :(=) && isexpr(e.args[2], :enter)))
            vars = Dict() # todo : needs to be recur func to allow new vars?
        elseif isexpr(e, :(=))
            if haskey(vars, e.args[1])
                delete!(vars, e.args[1])
                di[e.args[1]] = true
            end
        end
    end
    di
end

function for_each_isdefined(f, e)
    if isatom(e) || isquoted(e)
        false
    elseif isexpr(e, :isdefined)
        f(e.args[1])
    else
        foreach(x -> for_each_isdefined(f, x), e.args)
    end
end

format_loc(x) = x


isvalid_ir_argument(e) = issimple_atom(e) || issymbol(e) || e isa QuoteNode || (e isa Expr && e.head in (:quote, :inert, :top, :core, :globalref, :outerref, :slot, :static_parameter, :boundscheck))

isvalid_ir_value(lhs, e) = isssavalue(lhs) || 
                           isvalid_ir_argument(e) ||
                           (issymbol(lhs) && e isa Expr && e.head in (:new, :splatnew, :the_expection, :isdefined, :call, :invoke, :foreigncall, :cfunction, :gc_preserve_begin, :copyast, :new_opaque_closure))

isvalid_ir_return(e) = isvalid_ir_argument(e) || (e isa Expr && e.head === :lambda)
