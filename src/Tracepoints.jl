module Tracepoints

using Preferences

export @tracepoint, @region_start, @region_finish, @region

const PROBES_ENABLED = parse(Bool, @load_preference("default_enabled", "false"))

default_enabled(val::Bool) = @set_preferences!("default_enabled" => repr(val))

abstract type AbstractPayload end

@static if VERSION >= v"1.7-"
    mutable struct ShareableSemaphore
        @atomic value::Int
    end
else
    mutable struct ShareableSemaphore
        value::Threads.Atomic{Int}
        ShareableSemaphore(value::Int) = new(Threads.Atomic{Int}(value))
    end
end

struct TracepointSpec
    lineno::LineNumberNode
    argtypes::Vector{Type}
    payload::Base.RefValue{Ptr{Cvoid}}
    semaphore::ShareableSemaphore
end
TracepointSpec(lineno::LineNumberNode, argtypes::Vector, payload::Ptr{Cvoid}=C_NULL) =
    TracepointSpec(lineno, argtypes,
                   Ref(payload),
                   ShareableSemaphore(PROBES_ENABLED))
TracepointSpec(lineno::LineNumberNode, argtypes::Vector, payload::Base.RefValue{Int}, semaphore::ShareableSemaphore) =
    TracepointSpec(lineno, argtypes,
                   payload,
                   semaphore)

"""
    set!(f; kwargs...)
    set!(f, mod::Module; kwargs...)
    set!(f, mod::Module, category::Symbol; kwargs...)
    set!(f, mod::Module, category::Symbol, kind::Symbol; kwargs...)

Sets the probe payload for one or more tracepoints to `f`, which may either be
a function, or a pointer to a function. If `kind` is unspecified, then all
tracepoints with category `category` are programmed; if `category` is also
unspecified, then all tracepoints in `mod` are programmed. If `mod` is
unspecified, then all tracepoints in all loaded modules are programmed.

This function only programs the probe that tracepoints will call, but does not
enable those tracepoints; [`enable!`](@ref) must be called to cause the
tracepoints to execute their probe function.

If `f` is a `Ptr{Cvoid}`, an `abi` keyword argument must be passed to
communicate which ABI (`:fast`, `:slow`, or `:all` for both) the probe expects.
By default, any tracepoints with an incompatible ABI will generate a warning
and will be skipped. It's possible to change this behavior with the
`incompatible` keyword argument, which defaults to `:warn` but can also be set
to `:skip` (to quietly skip incompatible tracepoints) or `:error` (to throw an
error on incompatible tracepoints). Note that when `f` is a Julia function,
`abi` defaults to `:all`, although this can be changed to target only certain
ABIs.

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

function set!(f::Union{Base.Callable, Ptr{Cvoid}}; kwargs...)
    for mod in values(Base.loaded_modules)
        isdefined(mod, :__tracepoints_lock__) || continue
        set!(f, mod; kwargs...)
    end
end
function set!(f::Union{Base.Callable, Ptr{Cvoid}}, mod::Module; kwargs...)
    isdefined(mod, :__tracepoints_lock__) || return
    categories = lock(mod.__tracepoints_lock__) do
        collect(keys(mod.__tracepoints_specs__))
    end
    for category in categories
        set!(f, mod, category; kwargs...)
    end
    _recurse2(set!, f, mod; kwargs...)
end
function set!(payload::Ptr{Cvoid}, mod::Module, category::Symbol; abi::Symbol, incompatible::Symbol=:warn)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            validate_abi(spec, abi, incompatible) || continue
            spec.payload[] = payload
        end
    end
    _recurse2(set!, payload, mod, category; abi, incompatible)
end
function set!(payload::Ptr{Cvoid}, mod::Module, category::Symbol, kind::Symbol; abi::Symbol, incompatible::Symbol=:warn)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        spec = tracepoints[category][kind]
        validate_abi(spec, abi, incompatible) || return
        spec.payload[] = payload
    end
    _recurse2(set!, payload, mod, category, kind; abi, incompatible)
end
function set!(f, mod::Module, category::Symbol; abi::Symbol=:all, incompatible::Symbol=:warn)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    funcs = mod.__tracepoints_funcs__
    specs = lock(mod_lock) do
        tracepoints[category]
    end
    for (kind, spec) in specs
        validate_abi(spec, abi, incompatible) || continue
        ptr = generate_probe_fptr(f, spec)
        lock(mod_lock) do
            spec.payload[] = ptr
            funcs[category][kind] = f
        end
    end
    _recurse2(set!, f, mod, category; abi, incompatible)
end
function set!(f, mod::Module, category::Symbol, kind::Symbol; abi::Symbol=:all, incompatible::Symbol=:warn)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    funcs = mod.__tracepoints_funcs__
    spec = lock(mod_lock) do
        tracepoints[category][kind]
    end
    validate_abi(spec, abi, incompatible) || return
    ptr = generate_probe_fptr(f, spec)
    lock(mod_lock) do
        spec.payload[] = ptr
        funcs[category][kind] = f
    end
    _recurse2(set!, f, mod, category, kind; abi, incompatible)
end
function validate_abi(spec::TracepointSpec, abi::Symbol, incompatible::Symbol)
    if !(abi in (:fast, :slow, :all))
        throw(ArgumentError("Invalid value for `abi`: $abi (must be one of: `:slow`, `:fast`, `:all`)"))
    end
    spec_abi = determine_abi(spec)
    spec_abi_sym = spec_abi == :Any ? :slow : :fast
    if abi != :all && spec_abi_sym != abi
        if incompatible == :skip
            return false
        elseif incompatible == :warn
            @warn "Skipping incompatible ABI for tracepoint: probe ABI is $abi while tracepoint ABI is $spec_abi_sym"
            return false
        elseif incompatible == :error
            throw(ArgumentError("Incompatible ABI for tracepoint: probe ABI is $abi while tracepoint ABI is $spec_abi_sym"))
        else
            throw(ArgumentError("Invalid value for `incompatible`: $incompatible (must be one of: `:skip`, `:warn`, `:error`)"))
        end
    end
    return true
end
function generate_probe_fptr(@nospecialize(f), spec)
    abi_type = determine_abi(spec.argtypes)
    if abi_type != :Any
        # Fast ABIs
        if abi_type == :Nothing
            return eval(:(@cfunction($f, Int64, (String, Symbol, Symbol, Int64, Symbol, Int))))
        else
            # Null ABI
            return eval(:(@cfunction($f, Int64, (String, Symbol, Symbol, Int64, Symbol, $abi_type, Symbol))))
        end
    else
        # Slow ABI
        return eval(:(@cfunction($f, Int64, (String, Symbol, Symbol, Int64, Symbol, Any))))
    end
end

function enable!(mod::Module)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec_dict in values(tracepoints)
            for spec in values(spec_dict)
                adjust_semaphore!(spec.semaphore, 1)
            end
        end
    end
    _recurse1(enable!, mod)
end
function disable!(mod::Module)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec_dict in values(tracepoints)
            for spec in values(spec_dict)
                adjust_semaphore!(spec.semaphore, -1)
            end
        end
    end
    _recurse1(disable!, mod)
end
function enable!(mod::Module, category::Symbol)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            adjust_semaphore!(spec.semaphore, 1)
        end
    end
    _recurse1(enable!, mod, category)
end
function disable!(mod::Module, category::Symbol)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        for spec in values(tracepoints[category])
            adjust_semaphore!(spec.semaphore, -1)
        end
    end
    _recurse1(disable!, mod, category)
end
function enable!(mod::Module, category::Symbol, kind::Symbol)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        adjust_semaphore!(tracepoints[category][kind].semaphore, 1)
    end
    _recurse1(enable!, mod, category, kind)
end
function disable!(mod::Module, category::Symbol, kind::Symbol)
    isdefined(mod, :__tracepoints_lock__) || return
    mod_lock = mod.__tracepoints_lock__
    tracepoints = mod.__tracepoints_specs__
    lock(mod_lock) do
        adjust_semaphore!(tracepoints[category][kind].semaphore, -1)
    end
    _recurse1(disable!, mod, category, kind)
end

function _recurse1(f, mod, args...; kwargs...)
    for name in names(mod; all=true)
        isdefined(mod, name) || continue
        obj = getproperty(mod, name)
        if obj isa Module && obj !== mod
            f(obj, args...; kwargs...)
        end
    end
end
function _recurse2(f, arg1, mod, args...; kwargs...)
    for name in names(mod; all=true)
        isdefined(mod, name) || continue
        obj = getproperty(mod, name)
        if obj isa Module && obj !== mod
            f(arg1, obj, args...; kwargs...)
        end
    end
end

@static if VERSION >= v"1.7-"
    function adjust_semaphore!(semaphore::ShareableSemaphore, adj::Int)
        @atomic semaphore.value += adj
    end
    function probe_enabled(spec::TracepointSpec)
        semaphore = spec.semaphore
        return (@atomic semaphore.value) > 0
    end
else
    function adjust_semaphore!(semaphore::ShareableSemaphore, adj::Int)
        Threads.atomic_add!(semaphore.value, adj)
    end
    probe_enabled(spec::TracepointSpec) = spec.semaphore.value[] > 0
end
function probe_maybe_trigger(spec::TracepointSpec, modname::String, category::Symbol, kind::Symbol, lib_id::Int64, ::Val{abi_type}, arg, name::Symbol) where {abi_type}
    if probe_enabled(spec) && spec.payload[] != C_NULL
        probe_trigger(spec, modname, category, kind, lib_id, Val{abi_type}(), arg, name)
    else
        return 0
    end
end
@generated function probe_trigger(spec::TracepointSpec, modname::String, category::Symbol, kind::Symbol, lib_id::Int64, ::Val{abi_type}, arg, name::Symbol) where {abi_type}
    if abi_type != :Any
        if abi_type == :Nothing
            Targs = Expr(:tuple, :String, :Symbol, :Symbol, :Int64, :Symbol, :Int)
        else
            Targs = Expr(:tuple, :String, :Symbol, :Symbol, :Int64, :Symbol, abi_type, :Symbol)
        end
    else
        Targs = Expr(:tuple, :String, :Symbol, :Symbol, :Int64, :Symbol, :Any)
    end
    ex = Expr(:call, :ccall, :(spec.payload[]), :Int64, Targs)
    push!(ex.args, :(modname))
    push!(ex.args, :(category))
    push!(ex.args, :(kind))
    push!(ex.args, :(lib_id))
    push!(ex.args, QuoteNode(abi_type))
    if abi_type != :Any
        if abi_type == :Nothing
            push!(ex.args, :(0))
        else
            push!(ex.args, :(arg))
            push!(ex.args, :(name))
        end
    else
        push!(ex.args, :(arg))
    end
    return ex
end

function register_probe(mod::Module, category::Symbol, kind::Symbol, spec::TracepointSpec)
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
    argtypes = Type[]
    argvalues = []
    for arg in args.args
        if Meta.isexpr(arg, :(=))
            push!(argnames, arg.args[1].args[1])
            push!(argtypes, mod.eval(arg.args[1].args[2]))
            push!(argvalues, arg.args[2])
        elseif Meta.isexpr(arg, :(::))
            push!(argnames, arg.args[1])
            push!(argtypes, mod.eval(arg.args[2]))
            push!(argvalues, arg.args[1])
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
function determine_abi(argtypes)
    primitives = (UInt8, UInt16, UInt32, UInt64,
                  Int8, Int16, Int32, Int64,
                  Float16, Float32, Float64,
                  Symbol, String)
    if length(argtypes) == 0
        return :Nothing
    elseif length(argtypes) == 1 && only(argtypes) in primitives
        return nameof(only(argtypes))
    end
    return :Any
end
determine_abi(spec::TracepointSpec) = determine_abi(spec.argtypes)
function wrap_tracepoint_args(argspec)
    abi_type = determine_abi(argspec.argtypes)
    arg_name = :NONAME
    if abi_type == :Any
        T_nt = NamedTuple{(argspec.argnames...,), Tuple{argspec.argtypes...,}}
        args_ex = Expr(:tuple, argspec.argvalues...)
        args_box = :($T_nt($args_ex))
    elseif abi_type == :Nothing
        args_box = :()
    else
        args_box = only(argspec.argvalues)
        arg_name = only(argspec.argnames)
    end
    return (abi_type, args_box, arg_name)
end
function create_tracepoint_spec(source, argspec, args::Expr; alias_with=nothing)
    if alias_with === nothing
        return TracepointSpec(source, argspec.argtypes)
    else
        return TracepointSpec(source, argspec.argtypes,
                              alias_with.payload, alias_with.semaphore)
    end
end
function create_tracepoint!(mod::Module, source, category::Symbol, kind::Symbol, lib_id, args::Expr; alias_with=nothing)
    argspec = parse_args(mod, args)
    spec = create_tracepoint_spec(source, argspec, args; alias_with)
    register_probe(mod, category, kind, spec)
    return create_tracepoint_call(repr(mod), category, kind, lib_id, argspec, spec)
end
# Semaphore and probe payload not yet loaded
function create_tracepoint_call(modname, category, kind, lib_id, argspec, spec)
    abi_type, args_box, arg_name = wrap_tracepoint_args(argspec)
    return quote
        $probe_maybe_trigger($spec, $(QuoteNode(modname)), $(QuoteNode(category)), $(QuoteNode(kind)), $lib_id, $(Val{abi_type}()), $args_box, $(QuoteNode(arg_name)))
    end
end
# Semaphore and probe payload already loaded
function create_tracepoint_call_loaded(modname, category, kind, lib_id, argspec, spec, sema_set, payload)
    abi_type, args_box, arg_name = wrap_tracepoint_args(argspec)
    return quote
        if $sema_set && $payload != C_NULL
            $probe_trigger($spec, $(QuoteNode(modname)), $(QuoteNode(category)), $(QuoteNode(kind)), $lib_id, $(Val{abi_type}()), $args_box, $(QuoteNode(arg_name)))
        end
    end
end

macro tracepoint(kind::QuoteNode, category::QuoteNode, lib_id, args...)
    args = Expr(:tuple, args...)
    esc(create_tracepoint!(__module__, __source__, category.value, kind.value, lib_id, args))
end
macro region_start(category::QuoteNode, args...)
    args = Expr(:tuple, args...)
    esc(create_tracepoint!(__module__, __source__, category.value, :start, 0, args))
end
macro region_finish(category::QuoteNode, lib_id, args...)
    args = Expr(:tuple, args...)
    esc(create_tracepoint!(__module__, __source__, category.value, :finish, lib_id, args))
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
macro region(all_args...)
    fn_rewrap = Meta.isexpr(last(all_args), :function)
    if first(all_args) isa QuoteNode
        category, all_args... = all_args
        category = category.value
    elseif fn_rewrap
        category = last(all_args).args[1].args[1]::Symbol
    else
        throw(ArgumentError("@region: category must be a literal `Symbol` passed as the first argument, or `@region` must wrap a `function` definition"))
    end
    ex = last(all_args)
    args = Expr(:tuple, all_args[1:end-1]...)
    start_args, finish_args = parse_region_args(args)

    @gensym lib_id sema_set payload

    start_argspec = parse_args(__module__, start_args)
    start_spec = create_tracepoint_spec(__source__, start_argspec, start_args)
    register_probe(__module__, category, :start, start_spec)
    start_tp = create_tracepoint_call_loaded(repr(__module__), category, :start, 0, start_argspec, start_spec, sema_set, payload)

    finish_argspec = parse_args(__module__, finish_args)
    finish_spec = create_tracepoint_spec(__source__, finish_argspec, finish_args; alias_with=start_spec)
    register_probe(__module__, category, :finish, finish_spec)
    finish_tp = create_tracepoint_call_loaded(repr(__module__), category, :finish, lib_id, finish_argspec, finish_spec, sema_set, payload)

    if fn_rewrap
        ex.args[2] = quote
            $sema_set = $probe_enabled($start_spec)
            $payload = $start_spec.payload[]
            $lib_id = $start_tp
            $(Expr(:tryfinally, ex.args[2], finish_tp))
        end
        return esc(ex)
    else
        return esc(quote
            $sema_set = $probe_enabled($start_spec)
            $payload = $start_spec.payload[]
            $lib_id = $start_tp
            $(Expr(:tryfinally, ex, finish_tp))
        end)
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
