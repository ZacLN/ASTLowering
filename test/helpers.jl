using Test, Lowering, SExpressions, CSTParser

function stoExpr(s)
    if s isa List
        if isnil(s)
            ()
        elseif isnil(cdr(s))
            s = car(s)
            if s isa Symbol && String(s) == "true"
                true
            elseif s isa Symbol && String(s) == "false"
                false
            else
                s
            end
        else
            @assert car(s) isa Symbol
            Expr(car(s), [stoExpr(a) for a in cdr(s)]...)
        end
    else
        s
    end
end


function replace_reps(s)
    m = match(r"#(\d+)=", s)
    while m !== nothing
        io = IOBuffer(s)
        seek(io, m.offset + sizeof(m.match)-1)
        obj = SExpressions.Parser.nextobject(io)
        val = sprint(show, obj.value)
        s = replace(s, m.match => "", count = 1)
        s = replace(s, "#$(m.captures[1])#" => val)
        m = match(r"#(\d+)=", s)
    end
    s
end

function replace_strs(s)
    # m = match(r"#<julia: \\\"([\S\s]+)\\\">", s)
    # while m !== nothing
    #     s = replace(s, m.match => "\"$(m.captures[1])\"")
    #     m = match(r"#<julia: \\\"([\S\s]+)\\\">", s)
    #     m = match(r"(#(\d+)#)", s)
    # end
    # s
    m1 = findfirst("#<julia: \"", s)
    m1 === nothing && return s
    m2 = findnext("\">", s, last(m1) + 1)
    m2 === nothing && return s
    while true
        s = string(String(codeunits(s)[1:first(m1) - 1]), "\"", String(codeunits(s)[last(m1)+1:first(m2)-1]), "\"", String(codeunits(s)[last(m2) + 1: end]))
        m1 = findfirst("#<julia: \"", s)
        m1 === nothing && return s
        m2 = findnext("\">", s, last(m1) + 1)
        m2 === nothing && return s
    end
    s
end


function scm_lower(e)
    # requires build of julia w/ C interface to jl_expand0 that returns a string of the lowered code
    s = ccall(:jl_expand0, Any, (Any, Any), e, Main)
    if s isa Expr
        if s.head == :error
            s = "(error \"$(s.args[1])\")"
        else
            return s
        end
    end
    
    s = replace_reps(s)
    # replace Chars
    s = replace(s, r"#<julia: Char(\S*)>" => "#CHAR")
    s = replace_strs(s)

    m = match(r"#(\d+)#", s)
    while m !== nothing
        s = replace(s, r"#(\d+)#" => "(ssavalue $(m.captures[1]))")
        m = match(r"(#(\d+)#)", s)
    end

    m = match(r"#\d+=", s)
    while m !== nothing
        s = replace(s, r"#\d+=" => "")
        m = match(r"#\d+=", s)
    end
    s = replace(s, "(inert .)" => "(inert DOT)")

    l = SExpressions.Parser.parse(s)
    replace_nulls(stoExpr(l))
end


function compare_lowered(a, b)
    r = if a isa Expr && b isa Expr
        if a.head === b.head === :ssavalue
            true
        else
            compare_lowered(a.head, b.head) && all(x -> compare_lowered(x[1], x[2]), zip(a.args, b.args))
        end
    elseif a isa LineNumberNode && b isa LineNumberNode || (a isa LineNumberNode && b isa Expr && b.head == :line) || (b isa LineNumberNode && a isa Expr && a.head == :line)
        true
    elseif a isa Symbol && b isa Symbol
        a == b || 
        ((string(a) == "#self#" && string(b) == "_self_") || (string(b) == "#self#" && string(a) == "_self_")) || 
        (occursin(r"^#\d+$", String(a)) && occursin(r"^#\d+$", String(b))) ||
        (occursin(r"^#s\d+$", String(a)) && occursin(r"^#s\d+$", String(b))) ||
        equiv_namedsym(String(a), String(b)) || (a == :. && b == :DOT)
    elseif (a isa Char && b isa Symbol && String(b) == "#CHAR") || (b isa Char && a isa Symbol && String(a) == "#CHAR")
        true
    elseif a isa Bool && b isa Expr && b.head === :quote && b.args[1] isa Bool
        true
    elseif a isa String && b isa String
        true
    else
        a == b
    end
    !r && error(a,b)
    # !r && @info a, b
    r
end

function equiv_namedsym(a, b)
    ma = match(r"#(\S*)#\d+", a)
    ma === nothing && return false
    mb = match(r"#(\S*)#\d+", b)
    mb === nothing && return false
    ma.captures[1] == mb.captures[1]
end

using SExpressions.Parser: Dot, SExpression, skipws, skipcomment, nextobject, readobjectsuntil, listify, _READER_MACROS, parsestring, readsymbol, tryparse, closer
function SExpressions.Parser.nextobject(io::IO) :: Union{Some{<:Union{Dot, SExpression}}, Nothing}
    skipws(io)
    if eof(io)
        return nothing
    end

    c = peek(io, Char)
    if c == ';'
        skipcomment(io)
        nextobject(io)
    elseif c in "([{"
        read(io, Char)
        cl = closer(c)
        objects = readobjectsuntil(io, cl)
        Some(listify(objects))
    elseif c in ")]}"
        error("mismatched superfluous $c")
    elseif c in keys(_READER_MACROS)
        read(io, Char)
        nextobj = nextobject(io)
        if nextobj === nothing
            error("lonely reader macro $c")
        else
            Some(List(_READER_MACROS[c], something(nextobj)))
        end
    elseif c == '"'
        read(io, Char)
        Some(parsestring(io))
    # elseif c == '#'
    #     read(io, Char)
    #     Some(readhash(io))
    else
        str = readsymbol(io)
        if str == "."
            Some(Dot())
        else
            asnumber = tryparse(Number, str)
            Some(something(asnumber, Symbol(str)))
        end
    end
end

function test_file(f)
    s = String(read(f))
    @info f
    tl = CSTParser.remlineinfo!((do_replacementes(Meta.parseall(s))))
    for (i, e) in enumerate(tl.args)
        @info i
        l1 = Lowering.expand_forms(Lowering.julia_expand_macroscope(e))
        l2 = scm_lower(e)
        @test compare_lowered(l1, l2)
    end
end

function do_replacementes(x)
    if x isa Expr
        for (i,a) in enumerate(x.args)
            if a isa Expr && a.head == :string
                x.args[i] = Expr(:string)
            elseif a isa GlobalRef && a.mod == Core
                x.args[i] = Expr(:core, a.name)
            end
            do_replacementes(a)
        end
    end
    x
end

function replace_nulls(x)
    if x isa Expr
        for (i,a) in enumerate(x.args)
            if a == :null
                x.args[i] = nothing
            end
            replace_nulls(a)
        end
    end
    x
end


function replace_macrocalls(x)
    if x isa Expr
        for (i,a) in enumerate(x.args)
            if a isa Expr && a.head == :macrocall
                if length(a.args) > 2
                    x.args[i] = a.args[3]
                end
            end
            replace_macrocalls(a)
        end
    end
    x
end


macro test_lowering(e0)
    quote
        let e = CSTParser.remlineinfo!(replace_strings($(Expr(:quote,e0))))
            l1 = Lowering.expand_forms(e)
            l2 = scm_lower(e)
            @test compare_lowered(l1, l2)
        end
    end
end


function lower_recur_folder(dir)
    for (root, dirs, files) in walkdir(dir)
        for f in files
            if endswith(f, ".jl")
                s = String(read(joinpath(root, f)))
                t = time()
                tl = CSTParser.remlineinfo!(replace_macrocalls(do_replacementes(Meta.parseall(s))))
                t1 = time()
                for (i, e) in enumerate(tl.args)
                    Lowering.expand_forms(Lowering.julia_expand_macroscope(e))
                end
                
                @info string(rpad(f, 20), "  ", lpad(round((t1-t)*1000, sigdigits = 3), 10), "ms  ", round((time()-t1)*1000, sigdigits = 3), "ms  ")
            end
        end
    end
end

function lower_toplevel(e, N =1)
    for _ in 1:N
        for i in 1:length(e.args)
            Lowering.expand_forms(Lowering.julia_expand_macroscope(e.args[i]))
        end
    end
end