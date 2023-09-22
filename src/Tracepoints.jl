module Tracepoints

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

"""
    set!(f)
    set!(f, mod::Module)
    set!(f, mod::Module, category::Symbol)
    set!(f, mod::Module, category::Symbol, kind::Symbol)

Sets the probe payload for one or more tracepoints to `f`, which may either be
a function, or a pointer to a function. If `kind` is unspecified, then all
tracepoints with category `category` are programmed; if `category` is also
unspecified, then all tracepoints in `mod` are programmed. If `mod` is
unspecified, then all tracepoints in all loaded modules are programmed.

This function only programs the probe that tracepoints with call, but does not
enable those tracepoints; [`enable!`](@ref) must be called to cause the
tracepoints to execute their probe function.

Note that if `f` is not a `Ptr{Cvoid}`, it will be rooted until a future `set!`
call sets a different probe payload.
"""
function set! end

"""
    enable!(mod::Module)
    enable!(mod::Module, category::Symbol)
    enable!(mod::Module, category::Symbol, kind::Symbol)

Enables one or more tracepoints. If `kind` is unspecified, then all tracepoints
with category `category` are enabled; if `category` is also unspecified, then
all tracepoints in `mod` are enabled. If `mod` is unspecified, then all
tracepoints in all loaded modules are enabled.

This function only enables tracepoints, but does not program them with a probe
payload; [`set!`](@ref) must be called to program the tracepoints with an
appropriate probe.

This function is the counterpart to [`disable!`](ref), which can be called to
undo a call to `enable!`.
"""
function enable! end

"""
    disable!(mod::Module)
    disable!(mod::Module, category::Symbol)
    disable!(mod::Module, category::Symbol, kind::Symbol)

Disables one or more tracepoints. If `kind` is unspecified, then all tracepoints
with category `category` are disabled; if `category` is also unspecified, then
all tracepoints in `mod` are disabled. If `mod` is unspecified, then all
tracepoints in all loaded modules are disabled.

This function is the counterpart to [`enable!`](ref), which can be called to
undo a call to `disable!`.
"""
function disable! end

function set!(f::Union{Base.Callable, Ptr{Cvoid}})
    for mod in values(Base.loaded_modules)
        if isdefined(mod, :__tracepoints_lock__)
            set!(f, mod)
        end
    end
end
function set!(f::Union{Base.Callable, Ptr{Cvoid}}, mod::Module)
    categories = lock(mod.__tracepoints_lock__) do
        collect(keys(mod.__tracepoints_specs__))
    end
    for category in categories
        set!(f, mod, category)
    end
end
function set!(payload::Ptr{Cvoid}, mod::Module, category::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            spec.payload[] = payload
        end
    end
end
function set!(payload::Ptr{Cvoid}, mod::Module, category::Symbol, kind::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        tracepoints[category][kind].payload[] = payload
    end
end
function set!(f, mod::Module, category::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    funcs = mod.__tracepoints_funcs__
    specs = lock(mod_lock) do
        tracepoints[category]
    end
    for (kind, spec) in specs
        ptr = eval(:(@cfunction($f, Int64, (Symbol, Symbol, Int64, Any))))
        lock(mod_lock) do
            tracepoints[category][kind].payload[] = ptr
            funcs[category][kind] = f
        end
    end
end
function set!(f, mod::Module, category::Symbol, kind::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    funcs = mod.__tracepoints_funcs__
    spec = lock(mod_lock) do
        tracepoints[category][kind]
    end
    ptr = eval(:(@cfunction($f, Int64, (Symbol, Symbol, Int64, Any))))
    lock(mod_lock) do
        tracepoints[category][kind].payload[] = ptr
        funcs[category][kind] = f
    end
end

function enable!(mod::Module)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec_dict in values(tracepoints)
            for spec in values(spec_dict)
                Threads.atomic_add!(spec.semaphore, 1)
            end
        end
    end
end
function disable!(mod::Module)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec_dict in values(tracepoints)
            for spec in values(spec_dict)
                Threads.atomic_sub!(spec.semaphore, 1)
            end
        end
    end
end
function enable!(mod::Module, category::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            Threads.atomic_add!(spec.semaphore, 1)
        end
    end
end
function disable!(mod::Module, category::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            Threads.atomic_sub!(spec.semaphore, 1)
        end
    end
end
function enable!(mod::Module, category::Symbol, kind::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        Threads.atomic_add!(tracepoints[category][kind].semaphore, 1)
    end
end
function disable!(mod::Module, category::Symbol, kind::Symbol)
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
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
@generated function probe_trigger(spec::TracepointSpec, category::Symbol, kind::Symbol, lib_id::Int64, arg)
    Targs = Expr(:tuple, :Symbol, :Symbol, :Int64, :Any)
    ex = Expr(:call, :ccall, :(spec.payload[]), :Int64, Targs)
    push!(ex.args, :(category))
    push!(ex.args, :(kind))
    push!(ex.args, :(lib_id))
    push!(ex.args, :(arg))
    return ex
end

function register_probe(mod::Module, category::Symbol, kind::Symbol, spec::TracepointSpec; enable=false)
    if enable
        spec.semaphore[] = 1
    end
    if !isdefined(mod, :__tracepoints_lock__)
        mod_lock = mod.eval(:(__tracepoints_lock__ = Threads.ReentrantLock()))
        tracepoints = mod.eval(:(__tracepoints_specs__ = Dict{Symbol,Dict{Symbol,$TracepointSpec}}()))
        # Just for rooting of function objects
        funcs = mod.eval(:(__tracepoints_funcs__ = Dict{Symbol,Dict{Symbol,Any}}()))
    else
        mod_lock = mod.__tracepoints_lock__
        tracepoints = mod.__tracepoints_specs__
        funcs = mod.__tracepoints_funcs__
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
        elseif arg isa Expr
            throw(ArgumentError("Tracepoint argument unsupported: `Expr` with head: $(arg.head)"))
        elseif arg isa Symbol
            throw(ArgumentError("Tracepoint argument must have a type specifier: $arg"))
        else
            throw(ArgumentError("Tracepoint argument unsupported: $arg"))
        end
    end
    (;argnames, argtypes, argvalues)
end
function create_tracepoint!(mod::Module, source, category::Symbol, kind::Symbol, lib_id, args::Expr)
    argspec = parse_args(mod, args)
    spec = TracepointSpec(source, argspec.argtypes)
    register_probe(mod, category, kind, spec)
    T_nt = NamedTuple{(argspec.argnames...,), Tuple{argspec.argtypes...,}}
    args_box = Ref{T_nt}()
    args_ex = Expr(:tuple, argspec.argvalues...)
    return quote
        if $probe_enabled($spec)
            $args_box[] = $T_nt($args_ex)
            $probe_maybe_trigger($spec, $(QuoteNode(category)), $(QuoteNode(kind)), $lib_id, $args_box)
        end
    end
end
macro tracepoint(kind::QuoteNode, category::QuoteNode, lib_id, args=Expr(:tuple))
    create_tracepoint!(__module__, __source__, category.value, kind.value, lib_id, args)
end
macro region_start(category::QuoteNode, args=Expr(:tuple))
    create_tracepoint!(__module__, __source__, category.value, :start, 0, args)
end
macro region_finish(category::QuoteNode, lib_id, args=Expr(:tuple))
    create_tracepoint!(__module__, __source__, category.value, :finish, lib_id, args)
end

"""
    @region :category arg1 arg2... ex

Constructs a pair of tracepoints around the execution of `ex`. The start
tracepoint executes just before `ex`, and the finish tracepoint executes just
after `ex`. The category for both tracepoints is `:category`, and must be a
literal `Symbol` (as the tracepoints are constructed while `@region` is being
parsed). The kind for each tracepoint is `:start` and `:finish` respectively
(used when programming or enabling/disabling tracepoints).

These tracepoints start out disabled and unprogrammed, and by default will do
nothing (having negligible performance impact, if any). They can be programmed
with [`set!`](@ref), and enabled with [`enable!`](@ref).

Arguments may be provided in a few formats:

`arg::T` - This specifies that the argument with name `arg` has type `T`, where
`T` is a concrete type. In this form, `arg` must be a variable in scope that
`@region` can read during start and finish tracepoint execution. If `arg` is
modified during the execution of `ex`, its new value will be passed into the
finish tracepoint.

`arg::T=value` - This format is similar to `arg::T`, except that `arg` is not
read from a variable with the same name, but is instead hard-coded as `value`
for both start and finish tracepoints.

`(start_arg::ST, finish_arg::FT)` - This format is like `arg::T`, except that
it allows specifying different values for the start and finish tracepoints.
"""
macro region(category, _args...)
    if !(category isa QuoteNode)
        throw(ArgumentError("@region: category must be a literal `Symbol`"))
    end
    args = Expr(:tuple, _args[1:end-1]...)
    ex = _args[end]
    start_args, finish_args = parse_region_args(args)

    @gensym lib_id
    start_tp = create_tracepoint!(__module__, __source__, category.value, :start, 0, start_args)
    finish_tp = create_tracepoint!(__module__, __source__, category.value, :finish, lib_id, finish_args)

    quote
        # FIXME: Load semaphore and probe
        $lib_id = $start_tp
        try
            $(esc(ex))
        finally
            $finish_tp
        end
    end
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

end # module
