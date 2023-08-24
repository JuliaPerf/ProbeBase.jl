module ProbeBase

using Preferences

export @tracepoint, @region_start, @region_finish, @region

const PROBES_ENABLED = parse(Bool, @load_preference("default_enabled", "false"))

default_enabled(val::Bool) = @set_preferences!("default_enabled" => repr(val))

abstract type AbstractPayload end

struct TracepointSpec
    lineno::LineNumberNode
    argtypes::Vector{DataType}
    payload::Base.RefValue{Ptr{Cvoid}}
    semaphore::Threads.Atomic{Int}
end
TracepointSpec(lineno::LineNumberNode, argtypes::Vector, payload::Ptr{Cvoid}=C_NULL) =
    TracepointSpec(lineno, argtypes,
              Ref(payload),
              Threads.Atomic{Int}(PROBES_ENABLED))

function set!(payload::Ptr{Cvoid})
    for mod in values(Base.loaded_modules)
        if isdefined(mod, :__probebase_lock__)
            set!(mod, payload)
        end
    end
end
function set!(f::Base.Callable)
    for mod in values(Base.loaded_modules)
        if isdefined(mod, :__probebase_lock__)
            set!(f, mod)
        end
    end
end
function set!(mod::Module, payload::Ptr{Cvoid})
    categories = lock(mod.__probebase_lock__) do
        collect(keys(mod.__probebase_tracepoints__))
    end
    for category in categories
        set!(mod, category, payload)
    end
end
function set!(f::Base.Callable, mod::Module)
    categories = lock(mod.__probebase_lock__) do
        collect(keys(mod.__probebase_tracepoints__))
    end
    for category in categories
        set!(f, mod, category)
    end
end
function set!(mod::Module, category::Symbol, payload::Ptr{Cvoid})
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            spec.payload[] = payload
        end
    end
end
function set!(mod::Module, category::Symbol, kind::Symbol, payload::Ptr{Cvoid})
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        tracepoints[category][kind].payload[] = payload
    end
end
function set!(f, mod::Module, category::Symbol)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    funcs = mod.__probebase_funcs__
    specs = lock(mod_lock) do
        tracepoints[category]
    end
    for (kind, spec) in specs
        ptr = eval(:(@cfunction($f, Int64, (Symbol, Symbol, Int64, $(spec.argtypes...),))))
        lock(mod_lock) do
            tracepoints[category][kind].payload[] = ptr
            funcs[category][kind] = f
        end
    end
end
function set!(f, mod::Module, category::Symbol, kind::Symbol)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    funcs = mod.__probebase_funcs__
    spec = lock(mod_lock) do
        tracepoints[category][kind]
    end
    ptr = eval(:(@cfunction($f, Cvoid, ($(spec.argtypes...),))))
    lock(mod_lock) do
        tracepoints[category][kind].payload[] = ptr
        funcs[category][kind] = f
    end
end
function enable!(mod::Module)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        for spec_dict in values(tracepoints)
            for spec in values(spec_dict)
                Threads.atomic_add!(spec.semaphore, 1)
            end
        end
    end
end
function disable!(mod::Module)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        for spec_dict in values(tracepoints)
            for spec in values(spec_dict)
                Threads.atomic_sub!(spec.semaphore, 1)
            end
        end
    end
end
function enable!(mod::Module, category::Symbol)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            Threads.atomic_add!(spec.semaphore, 1)
        end
    end
end
function disable!(mod::Module, category::Symbol)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            Threads.atomic_sub!(spec.semaphore, 1)
        end
    end
end
function enable!(mod::Module, category::Symbol, kind::Symbol)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        Threads.atomic_add!(tracepoints[category][kind].semaphore, 1)
    end
end
function disable!(mod::Module, category::Symbol, kind::Symbol)
    mod_lock = mod.__probebase_lock__
    tracepoints = mod.__probebase_tracepoints__
    lock(mod_lock) do
        Threads.atomic_sub!(tracepoints[category][kind].semaphore, 1)
    end
end

probe_enabled(spec::TracepointSpec) = spec.semaphore[] > 0
function probe_maybe_trigger(spec::TracepointSpec, category::Symbol, kind::Symbol, lib_id::Int64, args...)
    if probe_enabled(spec)
        probe_trigger(spec, category, kind, lib_id, args...)
    end
end
@generated function probe_trigger(spec::TracepointSpec, category::Symbol, kind::Symbol, lib_id::Int64, args...)
    Targs = Expr(:tuple, :Symbol, :Symbol, :Int64, map(nameof, args)...)
    ex = Expr(:call, :ccall, :(spec.payload[]), :Int64, Targs)
    push!(ex.args, :(category))
    push!(ex.args, :(kind))
    push!(ex.args, :(lib_id))
    for (idx, arg) in enumerate(args)
        push!(ex.args, :(args[$idx]))
    end
    return ex
end

function register_probe(mod::Module, category::Symbol, kind::Symbol, spec::TracepointSpec; enable=false)
    if enable
        spec.semaphore[] = 1
    end
    if !isdefined(mod, :__probebase_lock__)
        mod_lock = mod.eval(:(__probebase_lock__ = Threads.ReentrantLock()))
        tracepoints = mod.eval(:(__probebase_tracepoints__ = Dict{Symbol,Dict{Symbol,$TracepointSpec}}()))
        funcs = mod.eval(:(__probebase_funcs__ = Dict{Symbol,Dict{Symbol,Any}}()))
    else
        mod_lock = mod.__probebase_lock__
        tracepoints = mod.__probebase_tracepoints__
        funcs = mod.__probebase_funcs__
    end
    lock(mod_lock) do
        module_cat_specs = get!(tracepoints, category) do
            Dict{Symbol,TracepointSpec}()
        end
        module_cat_specs[kind] = spec

        module_cat_funcs = get!(funcs, category) do
            Dict{Symbol,TracepointSpec}()
        end
        module_cat_funcs[kind] = nothing
    end
end
function parse_args(mod::Module, args)
    argnames = Symbol[]
    argtypes = DataType[]
    argvalues = Expr[]
    for arg in args.args
        if Meta.isexpr(arg, :(=))
            push!(argnames, arg.args[1].args[1])
            push!(argtypes, mod.eval(arg.args[1].args[2]))
            push!(argvalues, esc(arg.args[2]))
        elseif Meta.isexpr(arg, :(::))
            push!(argnames, arg.args[1])
            push!(argtypes, mod.eval(arg.args[2]))
            push!(argvalues, esc(arg.args[1]))
        else
            throw(ArgumentError("Cannot handle expr with head: $(arg.head)"))
        end
    end
    (;argnames, argtypes, argvalues)
end
function create_tracepoint!(mod::Module, source, category::Symbol, kind::Symbol, args::Expr)
    argspec = parse_args(mod, args)
    spec = TracepointSpec(source, argspec.argtypes)
    register_probe(mod, category, kind, spec)
    #args_nt_ex = E
    #@gensym args_nt
    return quote
        if $probe_enabled($spec)
            # FIXME: Pass lib_id
            #let $args_nt = NamedTuple($argspec.argvalues...)
                $probe_maybe_trigger($spec, $(QuoteNode(category)), $(QuoteNode(kind)), 0, $(argspec.argvalues...))
            #end
        end
    end
end
macro tracepoint(kind::QuoteNode, category::QuoteNode, args=Expr(:tuple))
    create_tracepoint!(__module__, __source__, category.value, kind.value, args)
end
macro region_start(category::QuoteNode, args=Expr(:tuple))
    create_tracepoint!(__module__, __source__, category.value, :start, args)
end
macro region_finish(category::QuoteNode, args=Expr(:tuple))
    create_tracepoint!(__module__, __source__, category.value, :finish, args)
end

function parse_region_args(args::Expr)
    start_args = Expr(:tuple)
    finish_args = Expr(:tuple)
    for arg in args.args
        if Meta.isexpr(arg, :(=)) && Meta.isexpr(arg.args[1], :tuple)
            push!(start_args.args, arg.args[1].args[1])
            push!(finish_args.args, arg.args[1].args[2])
        else
            push!(start_args.args, arg)
            push!(finish_args.args, arg)
        end
    end
    return start_args, finish_args
end
macro region(category::QuoteNode, _args...)
    args = Expr(:tuple, _args[1:end-1]...)
    ex = _args[end]
    start_args, finish_args = parse_region_args(args)
    quote
        $(create_tracepoint!(__module__, __source__, category.value, :start, start_args))
        try
            $(esc(ex))
        finally
            $(create_tracepoint!(__module__, __source__, category.value, :finish, finish_args))
        end
    end
end

end # module
