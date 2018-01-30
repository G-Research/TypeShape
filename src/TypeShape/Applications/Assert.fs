module TypeShape.Assert

// Adaptation of https://github.com/jet/xunit-jet

open System
open TypeShape.Core
open TypeShape.Core.Utils

exception EqualityAssertionException of message:string * path:string
  with
    override e.Message = sprintf "%s at %s" e.message e.path

module private DeepEqualityImpl =

    [<NoEquality; NoComparison>]
    type Breadcrumb =
        | Field of string
        | Index of obj
    with
        static member Format breadcrumb =
            match breadcrumb with
            | Field s -> s
            | Index i -> sprintf "[%A]" i

        static member Format (breadcrumbs:seq<Breadcrumb>) =
            breadcrumbs 
            |> Seq.map Breadcrumb.Format
            |> Seq.append [|"root"|]
            |> String.concat "."


    let mkExn (breadcrumbs : Breadcrumb list) (message : string) =
        let path = breadcrumbs |> List.rev |> Breadcrumb.Format
        EqualityAssertionException(message, path)

    let errorf breadcrumbs fmt = Printf.ksprintf (mkExn breadcrumbs >> raise) fmt

    let checkNull breadcrumbs (v1 : 'T) (v2 : 'T) =
        match v1 :> obj, v2 :> obj with
        | null, null -> true
        | null, _ 
        | _, null -> errorf breadcrumbs "Expected was %A but actual was %A." v1 v2
        | _ -> false

    let checkSize name breadcrumbs expectedLength actualLength =
        if expectedLength <> actualLength then
            errorf breadcrumbs "Expected %s length was %d but actual was %d." name expectedLength actualLength 

    /// Asserts for equality of expected and actual input
    type EqualityAsserter<'T> = Breadcrumb list -> 'T -> 'T -> unit

    let private cache = new TypeCache()

    let rec mkEqualityAssert<'T> () : EqualityAsserter<'T> =
        let mutable f = Unchecked.defaultof<EqualityAsserter<'T>>
        if cache.TryGetValue(&f) then f
        else
            use ctx = cache.CreateGenerationContext()
            mkEqualityAssertCached<'T> ctx

    and mkEqualityAssertCached<'T> (ctx : TypeGenerationContext) : EqualityAsserter<'T> =
        match ctx.InitOrGetCachedValue<EqualityAsserter<'T>> (fun c b t t' -> c.Value b t t') with
        | Cached(value = v) -> v
        | NotCached t ->
            let iterator = mkEqualityAssertInner<'T> ctx
            ctx.Commit t iterator

    /// Generates an Equality assertion checker for given type
    and mkEqualityAssertInner<'T> (ctx : TypeGenerationContext) : EqualityAsserter<'T> =
        let EQ (ecomp : EqualityAsserter<'a>) : EqualityAsserter<'T> = unbox ecomp

        let mkMemberComparer (m : IShapeMember<'T>) =
            m.Accept { new IMemberVisitor<'T, EqualityAsserter<'T>> with
                member __.Visit(shape : ShapeMember<'T, 'F>) =
                    let fc = mkEqualityAssertCached<'F> ctx
                    fun bc t1 t2 ->
                        let f1,f2 = shape.Project t1, shape.Project t2
                        fc (Field shape.Label :: bc) f1 f2 }

        match shapeof<'T> with
        | Shape.Array s when s.Rank = 1 ->
            s.Accept {
                new IArrayVisitor<EqualityAsserter<'T>> with
                    member __.Visit<'t> _ =
                        let ec = mkEqualityAssertCached<'t> ctx
                        fun bc (expected : 't[]) (actual : 't[]) ->
                            if checkNull bc expected actual then () else
                            checkSize "array" bc expected.Length actual.Length
                            (expected,actual) ||> Array.iteri2 (fun i t1 t2 -> ec (Index i :: bc) t1 t2)
                        |> EQ
            }

        | Shape.FSharpList s ->
            s.Accept {
                new IFSharpListVisitor<EqualityAsserter<'T>> with
                    member __.Visit<'t>() =
                        let ec = mkEqualityAssertCached<'t> ctx
                        fun bc (expected : 't list) (actual : 't list) ->
                            if checkNull bc expected actual then () else
                            checkSize "list" bc expected.Length actual.Length
                            (expected,actual) ||> List.iteri2 (fun i t1 t2 -> ec (Index i :: bc) t1 t2)
                        |> EQ
            }

        | Shape.FSharpSet s ->
            s.Accept {
                new IFSharpSetVisitor<EqualityAsserter<'T>> with
                    member __.Visit<'t when 't : comparison> () =
                        let ec = mkEqualityAssertCached<'t> ctx
                        fun bc (expected : Set<'t>) (actual : Set<'t>) ->
                            // |A| = |B| && A \subset B => A = B
                            if checkNull bc expected actual then () else
                            checkSize "set" bc expected.Count actual.Count
                            for e in expected do
                                if not <| actual.Contains e then
                                    errorf bc "Expected element %A." e
                        |> EQ
            }

        | Shape.FSharpMap s ->
            s.Accept {
                new IFSharpMapVisitor<EqualityAsserter<'T>> with
                    member __.Visit<'k, 'v when 'k : comparison> () =
                        let ec = mkEqualityAssertCached<'v> ctx
                        fun bc (expected : Map<'k,'v>) (actual : Map<'k,'v>) ->
                            // |A| = |B| && A \subset B => A = B
                            if checkNull bc expected actual then () else
                            checkSize "map" bc expected.Count actual.Count
                            for KeyValue(k,v) in expected do
                                match actual.TryFind k with
                                | None -> errorf bc "Expected key %A." k
                                | Some v' -> ec (Index k :: bc) v v'
                        |> EQ
            }

        | Shape.Enumerable s ->
            s.Accept {
                new IEnumerableVisitor<EqualityAsserter<'T>> with
                    member __.Visit<'Enum, 't when 'Enum :> seq<'t>> () =
                        let ec = mkEqualityAssertCached<'t> ctx
                        fun bc (expected : 'Enum) (actual : 'Enum) ->
                            if checkNull bc expected actual then () else
                            let expected,actual = Seq.toArray expected, Seq.toArray actual
                            checkSize "seq" bc expected.Length actual.Length
                            (expected,actual) ||> Array.iteri2 (fun i t1 t2 -> ec (Index i :: bc) t1 t2)
                        |> EQ
            }

        | Shape.Tuple (:? ShapeTuple<'T> as s) ->
            let isStruct = typeof<'T>.IsValueType
            let fcs = s.Elements |> Array.map mkMemberComparer
            fun bc t1 t2 -> 
                if isStruct && checkNull bc t1 t2 then () else
                for fc in fcs do fc bc t1 t2

        | Shape.FSharpRecord (:? ShapeFSharpRecord<'T> as s) ->
            let isStruct = typeof<'T>.IsValueType
            let fcs = s.Fields |> Array.map mkMemberComparer
            fun bc t1 t2 -> 
                if isStruct && checkNull bc t1 t2 then () else
                for fc in fcs do fc bc t1 t2

        | Shape.FSharpUnion (:? ShapeFSharpUnion<'T> as s) ->
            let isStruct = typeof<'T>.IsValueType
            let fcss = s.UnionCases |> Array.map (fun u -> u.Fields |> Array.map mkMemberComparer)
            fun bc u1 u2 ->
                if isStruct && checkNull bc u1 u2 then () else
                let tag1 = s.GetTag u1
                let tag2 = s.GetTag u2
                if tag1 <> tag2 then
                    let caseName t = s.UnionCases.[t].CaseInfo.Name
                    errorf bc "Expected union case %A but was %A" (caseName tag1) (caseName tag2)

                let fcs = fcss.[tag1]
                for fc in fcs do fc bc u1 u2

        | Shape.Equality s ->
            s.Accept { new IEqualityVisitor<EqualityAsserter<'T>> with
                member __.Visit<'t when 't : equality> () =
                    fun bc (e:'t) (a:'t) ->
                        if e <> a then
                            errorf bc "expected %A but was %A" e a
                    |> EQ }

        | _ ->
            fun bc e a ->
                let e,a = e :> obj, a :> obj
                if checkNull bc e a then () else
                if e.Equals a |> not then
                    errorf bc "expected %A but was %A" e a


/// <summary>
/// Performs a structural equality assertion, throwing an
/// EqualityAssertionException with detailed information on the location
/// of the mismatch within the object graph.
/// </summary>
/// <param name="expected">Expected object graph.</param>
/// <param name="actual">Actual object graph.</param>
let deepEquals (expected : 'T) (actual : 'T) : unit =
    DeepEqualityImpl.mkEqualityAssert<'T> () [] expected actual

/// <summary>
/// Performs a structural equality assertion, throwing an
/// EqualityAssertionException with detailed information on the location
/// of the mismatch within the object graph.
/// </summary>
/// <param name="expected">Expected object graph.</param>
/// <param name="actual">Actual object graph.</param>
let (===) (expected : 'T) (actual : 'T) = deepEquals expected actual