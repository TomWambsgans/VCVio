/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-!
# An encoded random oracle until a clash of encodings

A family of typed random oracles `spec` can be implemented by one random oracle `D →ₒ M`: a typed
point `t` is answered by the single oracle at its encoding `encode t`, truncated to the typed
range (`OracleComp.RandomOracleEncoding`). On the common interface
`unifSpec + (spec + (D →ₒ M))`, which also offers the raw inputs of the single oracle, this file
compares two worlds.

* The encoded world `RandomOracleEncoding.byteImpl` answers typed points and raw inputs by one
  lazy random oracle. It is the random oracle model of the single oracle after the program
  translation `RandomOracleEncoding.encodeImpl`
  (`RandomOracleEncoding.simulateQ_romImpl_simulateQ_encodeImpl`).
* The typed world `RandomOracleEncoding.typedImpl` answers typed points by independent lazy random
  oracles, and a raw input `x` by a router that reads it as the typed point `route x` and
  completes the typed answer there with a private value of `x`.

The two worlds agree until a clash, two cached typed points with the same encoding
(`RandomOracleEncoding.Clash`): an event of the output of the encoded world is at most the same
event, or a clash of the final typed cache, in the typed world
(`RandomOracleEncoding.prEvent_simulateQ_byteImpl_run_le`).

## Proof

The encoded world samples a whole value of `M` at the first touch of an encoding, while the typed
world samples only the typed answer, so no deterministic map of states relates the two. The
probabilistic map `RandomOracleEncoding.fill` reads a single-oracle cache off a typed state: it
queries the table of private values, as a lazy random oracle, at the encoding of every cached
typed point, and completes each typed answer with the value found there
(`RandomOracleEncoding.byteView`). A cache is a function, so a typed state can cache infinitely
many points, and drawing a value for each of them is then no finite computation; the fill is
meaningful only on the states with finitely many cached typed points, and the step condition is
stated on the invariant `RandomOracleEncoding.StateInv` through `QueryImpl.IntertwinesOn`.

The patched typed world `RandomOracleEncoding.patchedImpl` takes the steps of the typed world,
except on a step that creates a clash and from a state with a clash, where it fills, takes the
step of the encoded world and keeps the filled cache. The fill intertwines it with the encoded
world (`RandomOracleEncoding.intertwinesOn_fill_patchedImpl_byteImpl`); it agrees with the typed
world until a clash (`RandomOracleEncoding.agreeUntilBad_typedImpl_patchedImpl`); and
`QueryImpl.IntertwinesOn.prEvent_simulateQ_run_le_or_bad` combines the two. The steps commute
with the draws of the fill because queries to a lazy random oracle commute
(`randomOracle.evalDist_run_bind_simulateQ_run_swap`,
`randomOracle.evalDist_simulateQ_queryAll_run_bind_of_perm`), and a fresh typed answer completed
by a fresh private value is a fresh value of the single oracle
(`RandomOracleEncoding.evalDist_bind_complete`), which holds whenever every value of `M` splits
into a typed answer and a tail (`RandomOracleEncoding.ofSplit`).

## Main statements

- `OracleComp.RandomOracleEncoding`: an encoding of typed oracles into one oracle, with
  truncation, completion and the routing of raw inputs; `RandomOracleEncoding.ofSplit` builds one
  from a splitting of the single oracle's values.
- `RandomOracleEncoding.byteImpl`, `RandomOracleEncoding.typedImpl`: the encoded and the typed
  world.
- `RandomOracleEncoding.Clash`: two cached typed points share an encoding.
- `RandomOracleEncoding.prEvent_simulateQ_byteImpl_run_le`: the encoded world is bounded by the
  typed world or a clash; `RandomOracleEncoding.prEvent_simulateQ_romImpl_encodeImpl_run_le` is the
  same statement for the random oracle model of the single oracle after the encoding.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace OracleComp

/-- An encoding of a family of typed random oracles `spec` into one random oracle `D →ₒ M`.

A typed point `t` is encoded as the input `encode t` of the single oracle, and its typed answer
is the truncation `trunc t` of the `M`-valued answer there. Completing a typed answer `r` with a
value `p` of `M`, `complete t r p`, keeps what `trunc t` reads from `r` and the rest from `p`;
a uniform typed answer completed with an independent uniform value is a uniform value of `M`
whose truncation is the typed answer (`evalDist_bind_complete`). The partial map `route` reads a
raw input `x` as the typed point it encodes: it is defined on every encoding, and a typed point it
returns encodes `x`. -/
structure RandomOracleEncoding {ι : Type} (spec : OracleSpec ι) (D M : Type) [SampleableType M]
    [∀ t, SampleableType (spec.Range t)] where
  /-- The input of the single oracle that encodes a typed point. -/
  encode : ι → D
  /-- The typed answer read off a value of the single oracle. -/
  trunc : (t : ι) → M → spec.Range t
  /-- A value of the single oracle carrying a typed answer, completed from another value. -/
  complete : (t : ι) → spec.Range t → M → M
  /-- The typed point that a raw input of the single oracle is read as, if any. -/
  route : D → Option ι
  encode_eq_of_route_eq_some {x : D} {t : ι} : route x = some t → encode t = x
  isSome_route_encode (t : ι) : (route (encode t)).isSome
  trunc_complete (t : ι) (r : spec.Range t) (p : M) : trunc t (complete t r p) = r
  evalDist_bind_complete (t : ι) {γ : Type} [MeasurableSpace γ]
    (f : spec.Range t → M → ProbComp γ) :
    𝒟[do let r ← $ᵗ spec.Range t; let p ← $ᵗ M; f r (complete t r p)] =
      𝒟[do let w ← $ᵗ M; f (trunc t w) w]

namespace RandomOracleEncoding

/-! ## Encodings from splittings -/

section split

variable {ι M : Type} {spec : OracleSpec ι} [SampleableType M] [∀ t, SampleableType (spec.Range t)]
  {Tail : ι → Type} [∀ t, SampleableType (Tail t)]

/-- If a value of `M` splits into a typed answer and a tail, a uniform typed answer joined to the
tail of an independent uniform value of `M` is a uniform value of `M` whose first component is the
typed answer. -/
theorem evalDist_bind_symm_split (split : (t : ι) → M ≃ spec.Range t × Tail t) (t : ι)
    {γ : Type} [MeasurableSpace γ] (f : spec.Range t → M → ProbComp γ) :
    𝒟[do let r ← $ᵗ spec.Range t; let p ← $ᵗ M; f r ((split t).symm (r, (split t p).2))] =
      𝒟[do let w ← $ᵗ M; f (split t w).1 w] := by
  let _ : MeasurableSpace M := ⊤
  let _ : MeasurableSpace (spec.Range t × Tail t) := ⊤
  have hsplit : ∀ g : spec.Range t × Tail t → ProbComp γ,
      𝒟[$ᵗ M >>= fun w ↦ g (split t w)] = 𝒟[$ᵗ (spec.Range t × Tail t) >>= g] := fun g ↦
    evalDist_bind_bijective_uniform_cross _ _ SampleableType.evalDist_uniformSample
      SampleableType.evalDist_uniformSample (split t) (split t).bijective g
  have hprod : ∀ g : spec.Range t × Tail t → ProbComp γ,
      $ᵗ (spec.Range t × Tail t) >>= g =
        $ᵗ spec.Range t >>= fun r ↦ $ᵗ Tail t >>= fun τ ↦ g (r, τ) := fun g ↦ by
    simp [uniformSample_prod, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  calc _ = 𝒟[$ᵗ spec.Range t >>= fun r ↦ $ᵗ (spec.Range t × Tail t) >>= fun v ↦
        f r ((split t).symm (r, v.2))] :=
      evalDist_bind_congr_of_support _ _ _ fun r _ ↦
        hsplit fun v ↦ f r ((split t).symm (r, v.2))
    _ = 𝒟[$ᵗ spec.Range t >>= fun r ↦ $ᵗ Tail t >>= fun τ ↦ f r ((split t).symm (r, τ))] :=
      evalDist_bind_congr_of_support _ _ _ fun r _ ↦ by
        rw [hprod]
        exact OracleComp.evalDist_bind_const ($ᵗ spec.Range t)
          ($ᵗ Tail t >>= fun τ ↦ f r ((split t).symm (r, τ)))
    _ = 𝒟[$ᵗ (spec.Range t × Tail t) >>= fun v ↦ f v.1 ((split t).symm v)] := by rw [hprod]
    _ = _ := by
      rw [← hsplit]
      simp

variable {D : Type}

/-- The encoding of `spec` into `D →ₒ M` by `encode` and `route` in which every value of `M`
splits, for each typed point `t`, into a typed answer at `t` and a tail in `Tail t`: truncating
takes the typed answer, and completing a typed answer joins it to the tail of the completing
value. -/
@[expose] noncomputable def ofSplit (encode : ι → D) (route : D → Option ι)
    (encode_eq_of_route_eq_some : ∀ {x t}, route x = some t → encode t = x)
    (isSome_route_encode : ∀ t, (route (encode t)).isSome)
    (split : (t : ι) → M ≃ spec.Range t × Tail t) : RandomOracleEncoding spec D M where
  encode := encode
  trunc t w := (split t w).1
  complete t r p := (split t).symm (r, (split t p).2)
  route := route
  encode_eq_of_route_eq_some := encode_eq_of_route_eq_some
  isSome_route_encode := isSome_route_encode
  trunc_complete t r p := by simp
  evalDist_bind_complete t _ _ f := evalDist_bind_symm_split split t f

end split

variable {ι D M : Type} {spec : OracleSpec ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)] [DecidableEq ι] [DecidableEq D]
  (E : RandomOracleEncoding spec D M)

/-! ## The two worlds -/

/-- The typed oracles answered through the single random oracle: a typed point is the query at
its encoding, truncated. -/
@[expose] noncomputable def encodedImpl : QueryImpl spec (StateT (D →ₒ M).QueryCache ProbComp) :=
  fun t ↦ E.trunc t <$> (D →ₒ M).randomOracle (E.encode t)

/-- The typed oracles and the raw inputs answered by the single random oracle. -/
@[expose] noncomputable def byteHashImpl :
    QueryImpl (spec + (D →ₒ M)) (StateT (D →ₒ M).QueryCache ProbComp) :=
  E.encodedImpl + (D →ₒ M).randomOracle

/-- The encoded world: uniform sampling passes through, typed points and raw inputs are answered
by the single random oracle. -/
@[expose] noncomputable def byteImpl :
    QueryImpl (unifSpec + (spec + (D →ₒ M))) (StateT (D →ₒ M).QueryCache ProbComp) :=
  unifFwdImpl (D →ₒ M) + E.byteHashImpl

/-- The encoding as a program translation: a uniform query and a raw input are the same query of
`unifSpec + (D →ₒ M)`, and a typed point is the query of the single oracle at its encoding,
truncated. -/
@[expose] def encodeImpl :
    QueryImpl (unifSpec + (spec + (D →ₒ M))) (OracleComp (unifSpec + (D →ₒ M)))
  | .inl n => (query (spec := unifSpec + (D →ₒ M)) (.inl n) : OracleComp _ (Fin (n + 1)))
  | .inr (.inl t) => E.trunc t <$> (query (spec := unifSpec + (D →ₒ M)) (.inr (E.encode t)) :
      OracleComp _ M)
  | .inr (.inr x) => (query (spec := unifSpec + (D →ₒ M)) (.inr x) : OracleComp _ M)

/-- Independent lazy random oracles for the typed points and for a private table of the raw
inputs, on the pair of their caches. -/
@[expose] noncomputable def pairImpl : QueryImpl (spec + (D →ₒ M))
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  QueryImpl.parallelStateT spec.randomOracle (D →ₒ M).randomOracle

/-- The router: a raw input `x` draws its private value `p`; if `x` is read as a typed point `q`,
the answer is the typed answer at `q` completed from `p`, and otherwise it is `p`. -/
@[expose] noncomputable def routerImpl :
    QueryImpl (D →ₒ M) (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  fun x ↦ do
    let p ← (pairImpl (spec := spec) (D := D) (M := M) (.inr x) :
      StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp M)
    match E.route x with
    | some q => (E.complete q · p) <$> (pairImpl (D := D) (M := M) (.inl q) :
        StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp (spec.Range q))
    | none => pure p

/-- The typed oracles answered by independent lazy random oracles, and the raw inputs by the
router. -/
@[expose] noncomputable def typedHashImpl :
    QueryImpl (spec + (D →ₒ M)) (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  (fun t ↦ pairImpl (spec := spec) (D := D) (M := M) (.inl t)) + E.routerImpl

/-- The typed world: uniform sampling passes through, typed points are answered by independent
lazy random oracles and raw inputs by the router. -/
@[expose] noncomputable def typedImpl : QueryImpl (unifSpec + (spec + (D →ₒ M)))
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) + E.typedHashImpl

/-! ## Clashes and the byte view of a typed state -/

/-- Two distinct cached typed points share an encoding. -/
@[expose] def Clash (c : spec.QueryCache) : Prop :=
  ∃ q q', q ≠ q' ∧ (c q).isSome ∧ (c q').isSome ∧ E.encode q = E.encode q'

/-- Some cached typed point is encoded as `x`. -/
@[expose] def Covered (c : spec.QueryCache) (x : D) : Prop :=
  ∃ q, E.encode q = x ∧ (c q).isSome

open Classical in
/-- The single-oracle cache that a typed cache `c` and a table `pv` describe: at a tabulated
input covered by a cached typed point, the typed answer completed from the tabulated value, and
at any other tabulated input, the tabulated value. -/
noncomputable def byteView (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (D →ₒ M).QueryCache :=
  .ofFn fun x ↦ (pv x).map fun p ↦
    if h : E.Covered c x then ((c h.choose).map fun r ↦ E.complete h.choose r p).getD p else p

open Classical in
/-- The single-oracle cache of a typed state, drawing what the typed state leaves open. Without a
clash and with finitely many cached typed points, the table is queried, as a lazy random oracle,
at the encoding of each cached typed point, and the result is read through `byteView`; with a
clash the table is the single-oracle cache itself. -/
noncomputable def fill (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    ProbComp (D →ₒ M).QueryCache :=
  if E.Clash s.1 then pure s.2 else
    if h : {q | (s.1 q).isSome}.Finite then
      (fun w ↦ E.byteView s.1 w.2) <$> (simulateQ (D →ₒ M).randomOracle
        ((D →ₒ M).queryAll (h.toFinset.toList.map E.encode))).run s.2
    else pure ∅

/-- The step of the typed world at `u` caches a new typed point whose encoding is already
covered. -/
def Collides (c : spec.QueryCache) : (spec + (D →ₒ M)).Domain → Prop
  | .inl t => c t = none ∧ E.Covered c (E.encode t)
  | .inr x => ∃ q, E.route x = some q ∧ c q = none ∧ E.Covered c x

/-- The typed cache after a step at `u` answered by `a`, recording the typed point that the step
of the typed world would cache. -/
def mark (c : spec.QueryCache) :
    (u : (spec + (D →ₒ M)).Domain) → (spec + (D →ₒ M)).Range u → spec.QueryCache
  | .inl t, a => c.cacheQuery t a
  | .inr x, a => match E.route x with
    | some q => c.cacheQuery q (E.trunc q a)
    | none => c

open Classical in
/-- The typed world patched to follow the encoded world through `fill` on the steps that create a
clash and from states with a clash: such a step fills the single-oracle cache, takes the step of
the encoded world there, keeps the filled cache as its table and records the queried typed point. -/
noncomputable def patchedHashImpl :
    QueryImpl (spec + (D →ₒ M)) (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  fun u ↦ StateT.mk fun s ↦
    if E.Clash s.1 ∨ E.Collides s.1 u then do
      let b ← E.fill s
      let z ← (E.byteHashImpl u).run b
      pure (z.1, (E.mark s.1 u z.1, z.2))
    else (E.typedHashImpl u).run s

/-- The patched typed world on the whole interface. -/
noncomputable def patchedImpl : QueryImpl (unifSpec + (spec + (D →ₒ M)))
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) + E.patchedHashImpl

/-- The invariant of the patched typed world: finitely many typed points are cached, and without
a clash every tabulated raw input read as a typed point has that point cached. -/
def StateInv (s : spec.QueryCache × (D →ₒ M).QueryCache) : Prop :=
  {q | (s.1 q).isSome}.Finite ∧
    (¬E.Clash s.1 → ∀ x, (s.2 x).isSome → ∀ q, E.route x = some q → (s.1 q).isSome)

/-! ## Steps of the two worlds -/

section steps

variable {E}

omit [∀ t, SampleableType (spec.Range t)] in
/-- A uniform query lifted to a stateful handler samples and keeps the state. -/
theorem unifLift_run {σ : Type} (n : ℕ) (s : σ) :
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)) n).run s =
      (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp

/-- A typed query of the typed world queries the typed lazy random oracle on the typed cache. -/
theorem typedHashImpl_inl_run (t : ι) (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    (E.typedHashImpl (.inl t)).run s =
      (fun z ↦ (z.1, (z.2, s.2))) <$> (spec.randomOracle t).run s.1 := by
  obtain ⟨c, pv⟩ := s
  rfl

/-- A raw input of the typed world draws its private value, then completes the typed answer at the
typed point it is read as, if any. -/
theorem typedHashImpl_inr_run (x : D) (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    (E.typedHashImpl (.inr x)).run s =
      ((D →ₒ M).randomOracle x).run s.2 >>= fun z ↦ match E.route x with
        | some q => (fun y ↦ (E.complete q y.1 z.1, (y.2, z.2))) <$>
            (spec.randomOracle q).run s.1
        | none => pure (z.1, (s.1, z.2)) := by
  obtain ⟨c, pv⟩ := s
  simp only [typedHashImpl, QueryImpl.add_apply_inr, routerImpl, StateT.run_bind]
  change ((fun z ↦ (z.1, (c, z.2))) <$> ((D →ₒ M).randomOracle x).run pv) >>= _ = _
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun z ↦ ?_
  cases E.route x with
  | some q =>
    simp only [StateT.run_bind, Function.comp_apply, StateT.run_pure]
    change ((fun y ↦ (y.1, (y.2, z.2))) <$> (spec.randomOracle q).run c) >>= _ = _
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    rfl
  | none => rfl

omit [DecidableEq ι] in
/-- A typed query of the encoded world is the truncated query at its encoding. -/
theorem byteHashImpl_inl_run (t : ι) (b : (D →ₒ M).QueryCache) :
    (E.byteHashImpl (.inl t)).run b =
      (fun z ↦ (E.trunc t z.1, z.2)) <$> ((D →ₒ M).randomOracle (E.encode t)).run b := by
  simp only [byteHashImpl, QueryImpl.add_apply_inl, encodedImpl, StateT.run_map]

omit [DecidableEq ι] in
/-- A raw input of the encoded world is the query of the single oracle. -/
theorem byteHashImpl_inr_run (x : D) (b : (D →ₒ M).QueryCache) :
    (E.byteHashImpl (.inr x)).run b = ((D →ₒ M).randomOracle x).run b := by
  simp only [byteHashImpl, QueryImpl.add_apply_inr]

omit [DecidableEq ι] in
/-- The encoded world answers typed points and raw inputs by the single random oracle. -/
theorem byteImpl_apply_inr (u : (spec + (D →ₒ M)).Domain) :
    E.byteImpl (.inr u) = E.byteHashImpl u := rfl

/-- The typed world answers typed points and raw inputs by `typedHashImpl`. -/
theorem typedImpl_apply_inr (u : (spec + (D →ₒ M)).Domain) :
    E.typedImpl (.inr u) = E.typedHashImpl u := rfl

omit [DecidableEq ι] in
/-- A uniform query of the encoded world samples and keeps the cache. -/
theorem byteImpl_inl_run (n : ℕ) (b : (D →ₒ M).QueryCache) :
    (E.byteImpl (.inl n)).run b =
      (fun u ↦ (u, b)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) :=
  unifLift_run n b

/-- A uniform query of the typed world samples and keeps the state. -/
theorem typedImpl_inl_run (n : ℕ) (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    (E.typedImpl (.inl n)).run s =
      (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) :=
  unifLift_run n s

/-- A uniform query of the patched typed world samples and keeps the state. -/
theorem patchedImpl_inl_run (n : ℕ) (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    (E.patchedImpl (.inl n)).run s =
      (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) :=
  unifLift_run n s

omit [DecidableEq ι] in
/-- The encoded world is the random oracle model of the single oracle after the encoding. -/
theorem romImpl_compose_encodeImpl : (D →ₒ M).romImpl ∘ₛ E.encodeImpl = E.byteImpl := by
  funext u
  rcases u with n | t | x
  · rfl
  · rfl
  · simp [encodeImpl, byteImpl, byteHashImpl]

omit [DecidableEq ι] in
/-- Running the encoding of a computation in the random oracle model of the single oracle is
running the computation in the encoded world. -/
theorem simulateQ_romImpl_simulateQ_encodeImpl {α : Type}
    (oa : OracleComp (unifSpec + (spec + (D →ₒ M))) α) :
    simulateQ (D →ₒ M).romImpl (simulateQ E.encodeImpl oa) = simulateQ E.byteImpl oa := by
  rw [← QueryImpl.simulateQ_compose, romImpl_compose_encodeImpl]

end steps

/-! ## Clashes and the byte view -/

section view

variable {E}

omit [DecidableEq ι] [DecidableEq D] in
/-- A clash survives any change of the typed cache that keeps every cached point cached. -/
theorem Clash.mono {c c' : spec.QueryCache} (h : ∀ q, (c q).isSome → (c' q).isSome)
    (hc : E.Clash c) : E.Clash c' := by
  obtain ⟨q, q', hne, hq, hq', he⟩ := hc
  exact ⟨q, q', hne, h q hq, h q' hq', he⟩

omit [DecidableEq D] in
/-- Caching a new typed point whose encoding is covered creates a clash. -/
theorem clash_cacheQuery_of_covered {c : spec.QueryCache} {q : ι} (hq : c q = none)
    (hcov : E.Covered c (E.encode q)) (r : spec.Range q) : E.Clash (c.cacheQuery q r) := by
  obtain ⟨q', he, hq'⟩ := hcov
  have hne : q' ≠ q := by rintro rfl; simp [hq] at hq'
  refine ⟨q', q, hne, ?_, by simp, he⟩
  rwa [QueryCache.cacheQuery_of_ne _ _ hne]

omit [DecidableEq D] in
/-- Caching a typed point whose encoding is not covered creates no clash. -/
theorem not_clash_cacheQuery {c : spec.QueryCache} {q : ι} (hc : ¬E.Clash c)
    (hcov : ¬E.Covered c (E.encode q)) (r : spec.Range q) : ¬E.Clash (c.cacheQuery q r) := by
  rintro ⟨q₁, q₂, hne, h₁, h₂, he⟩
  rw [QueryCache.isSome_cacheQuery_apply_iff] at h₁ h₂
  rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
  · exact hne rfl
  · exact hcov ⟨q₂, he.symm, h₂⟩
  · exact hcov ⟨q₁, he, h₁⟩
  · exact hc ⟨q₁, q₂, hne, h₁, h₂, he⟩

omit [DecidableEq ι] [DecidableEq D] in
/-- The byte view at an input no cached typed point encodes is the table entry. -/
theorem byteView_apply_of_not_covered {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {x : D}
    (h : ¬E.Covered c x) : E.byteView c pv x = pv x := by
  simp [byteView, h]

omit [DecidableEq ι] [DecidableEq D] in
/-- Without a clash, the byte view at the encoding of a cached typed point is the table entry
completed by its typed answer. -/
theorem byteView_apply_encode {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {q : ι}
    {r : spec.Range q} (hc : ¬E.Clash c) (hq : c q = some r) :
    E.byteView c pv (E.encode q) = (pv (E.encode q)).map (E.complete q r) := by
  have hcov : E.Covered c (E.encode q) := ⟨q, rfl, by simp [hq]⟩
  simp only [byteView, QueryCache.ofFn_apply, hcov, ↓reduceDIte]
  congr 1
  funext p
  have key : ∀ q', E.encode q' = E.encode q → (c q').isSome →
      ((c q').map fun r' ↦ E.complete q' r' p).getD p = E.complete q r p := by
    intro q' he hs
    by_cases hne : q' = q
    · subst hne
      simp [hq]
    · exact absurd ⟨q', q, hne, hs, by simp [hq], he⟩ hc
  exact key _ hcov.choose_spec.1 hcov.choose_spec.2

omit [DecidableEq ι] in
/-- Tabulating an input no cached typed point encodes tabulates it in the byte view. -/
theorem byteView_cacheQuery_of_not_covered {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache}
    {x : D} (h : ¬E.Covered c x) (p : M) :
    E.byteView c (pv.cacheQuery x p) = (E.byteView c pv).cacheQuery x p := by
  refine QueryCache.ext fun x' ↦ ?_
  by_cases hx : x' = x
  · subst hx
    rw [byteView_apply_of_not_covered h]
    simp
  · simp [byteView, QueryCache.cacheQuery_of_ne _ _ hx]

/-- Without a clash, caching a typed point `q` with an uncovered encoding and tabulating its
encoding tabulates there, in the byte view, the typed answer completed from the table entry. -/
theorem byteView_cacheQuery_cacheQuery {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {q : ι}
    (hc : ¬E.Clash c) (hcov : ¬E.Covered c (E.encode q)) (r : spec.Range q) (p : M) :
    E.byteView (c.cacheQuery q r) (pv.cacheQuery (E.encode q) p) =
      (E.byteView c pv).cacheQuery (E.encode q) (E.complete q r p) := by
  have hc' := not_clash_cacheQuery hc hcov r
  refine QueryCache.ext fun x ↦ ?_
  by_cases hx : x = E.encode q
  · subst hx
    rw [byteView_apply_encode hc' (QueryCache.cacheQuery_self _ _ _)]
    simp
  · rw [QueryCache.cacheQuery_of_ne _ _ hx]
    by_cases hx' : E.Covered c x
    · obtain ⟨q', rfl, hs⟩ := hx'
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hs
      have hne : q' ≠ q := by rintro rfl; exact hx rfl
      rw [byteView_apply_encode hc' (r := r') (by rwa [QueryCache.cacheQuery_of_ne _ _ hne]),
        byteView_apply_encode hc hr', QueryCache.cacheQuery_of_ne _ _ hx]
    · have hx'' : ¬E.Covered (c.cacheQuery q r) x := by
        rintro ⟨q', he, hs⟩
        rw [QueryCache.isSome_cacheQuery_apply_iff] at hs
        rcases hs with rfl | hs
        · exact hx he.symm
        · exact hx' ⟨q', he, hs⟩
      rw [byteView_apply_of_not_covered hx'', byteView_apply_of_not_covered hx',
        QueryCache.cacheQuery_of_ne _ _ hx]

omit [DecidableEq ι] in
/-- At an input no cached typed point encodes, querying the single oracle on the byte view is
querying the table and reading the result through the byte view. -/
theorem randomOracle_run_byteView {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {x : D}
    (h : ¬E.Covered c x) :
    ((D →ₒ M).randomOracle x).run (E.byteView c pv) =
      (fun z ↦ (z.1, E.byteView c z.2)) <$> ((D →ₒ M).randomOracle x).run pv := by
  rw [_root_.randomOracle.run_eq, _root_.randomOracle.run_eq, byteView_apply_of_not_covered h]
  cases pv x with
  | some p => simp
  | none => simp [byteView_cacheQuery_of_not_covered h]

end view

/-! ## The fill -/

section fill

variable {E}

omit [DecidableEq ι] in
/-- The fill of a typed state with a clash is its table. -/
theorem fill_of_clash {s : spec.QueryCache × (D →ₒ M).QueryCache} (h : E.Clash s.1) :
    E.fill s = pure s.2 := by
  simp [fill, h]

omit [DecidableEq ι] in
/-- The fill of a typed state without a clash and with finitely many cached typed points queries
the table at their encodings and reads the result through the byte view. -/
theorem fill_of_not_clash {s : spec.QueryCache × (D →ₒ M).QueryCache} (h : ¬E.Clash s.1)
    (hf : {q | (s.1 q).isSome}.Finite) :
    E.fill s = (fun w ↦ E.byteView s.1 w.2) <$> (simulateQ (D →ₒ M).randomOracle
      ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run s.2 := by
  simp only [fill, h, hf, ↓reduceIte, ↓reduceDIte]

omit [DecidableEq ι] in
/-- The fill of the empty typed state is the empty cache. -/
theorem fill_empty : E.fill (∅, ∅) = pure ∅ := by
  have hc : ¬E.Clash (∅ : spec.QueryCache) := by
    rintro ⟨q, _, _, hq, _⟩
    simp at hq
  have hf : {q | ((∅ : spec.QueryCache) q).isSome}.Finite := by simp
  rw [fill_of_not_clash hc hf]
  have h0 : hf.toFinset = ∅ := by simp
  simp only [h0, Finset.toList_empty, List.map_nil, OracleSpec.queryAll_nil, simulateQ_pure,
    StateT.run_pure, map_pure]
  exact congrArg pure (QueryCache.ext fun x ↦ by simp [byteView])

omit [DecidableEq ι] [DecidableEq D] in
/-- The inputs the fill queries are the encodings covered by cached typed points. -/
theorem mem_map_encode_toList_iff {c : spec.QueryCache} (hf : {q | (c q).isSome}.Finite)
    (x : D) : x ∈ hf.toFinset.toList.map E.encode ↔ E.Covered c x := by
  simp only [List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    Covered]
  exact ⟨fun ⟨q, hq, he⟩ ↦ ⟨q, he, hq⟩, fun ⟨q, he, hq⟩ ↦ ⟨q, hq, he⟩⟩

omit [∀ t, SampleableType (spec.Range t)] [DecidableEq ι] in
/-- After the table is queried at the inputs of `L`, every input of `L` is tabulated and every
other input keeps its entry. -/
theorem apply_of_mem_support_queryAll {L : List D} {pv : (D →ₒ M).QueryCache}
    {w : Unit × (D →ₒ M).QueryCache}
    (hw : w ∈ support ((simulateQ (D →ₒ M).randomOracle ((D →ₒ M).queryAll L)).run pv)) (x : D) :
    (x ∈ L → (w.2 x).isSome) ∧ (x ∉ L → w.2 x = pv x) := by
  obtain ⟨hle, hiff⟩ := QueryImpl.withCaching_queryAll_le_and_isSome_iff uniformSampleImpl hw
  refine ⟨fun hx ↦ (hiff x).2 (.inr hx), fun hx ↦ ?_⟩
  cases hpv : pv x with
  | some v => exact hle hpv
  | none =>
    have := (hiff x).not.2 (by simp [hpv, hx])
    simpa using this

/-- Caching a typed point `q` with an uncovered encoding fills by querying the table at the
encoding of `q` first and then at the encodings of the other cached typed points. -/
theorem evalDist_fill_cacheQuery_bind {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {q : ι}
    (hc : ¬E.Clash c) (hf : {q | (c q).isSome}.Finite) (hcov : ¬E.Covered c (E.encode q))
    (r : spec.Range q) {γ : Type} [MeasurableSpace γ] (g : (D →ₒ M).QueryCache → ProbComp γ) :
    𝒟[E.fill (c.cacheQuery q r, pv) >>= g] =
      𝒟[((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
        (simulateQ (D →ₒ M).randomOracle ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run
          z.2 >>= fun w ↦ g (E.byteView (c.cacheQuery q r) w.2)] := by
  have hq : c q = none := by
    cases hcq : c q with
    | none => rfl
    | some _ => exact absurd ⟨q, rfl, by simp [hcq]⟩ hcov
  have hf' : {q' | ((c.cacheQuery q r) q').isSome}.Finite := by
    refine (hf.insert q).subset fun q' hq' ↦ ?_
    simp only [Set.mem_ofPred_eq, QueryCache.isSome_cacheQuery_apply_iff] at hq'
    simpa using hq'
  have hset : hf'.toFinset = insert q hf.toFinset := by
    ext q'
    simp [QueryCache.isSome_cacheQuery_apply_iff]
  have hperm : (hf'.toFinset.toList.map E.encode).Perm
      (E.encode q :: hf.toFinset.toList.map E.encode) := by
    rw [hset, ← List.map_cons]
    exact (Finset.toList_insert (by simp [hq])).map _
  rw [fill_of_not_clash (not_clash_cacheQuery hc hcov r) hf', bind_map_left]
  refine (_root_.randomOracle.evalDist_simulateQ_queryAll_run_bind_of_perm hperm pv
    fun b ↦ g (E.byteView (c.cacheQuery q r) b)).trans ?_
  simp only [OracleSpec.queryAll_cons, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run_bind, bind_assoc]

end fill

/-! ## The intertwining -/

section intertwining

variable {E}

/-- A fresh typed answer at a point `q` with an uncovered, untabulated encoding, a fresh table
entry there and the fill of the other cached typed points, read through the byte view, are a
fresh value of the single oracle at the encoding of `q`, truncated to the typed answer, after the
fill. -/
private theorem evalDist_fresh {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {q : ι}
    (hc : ¬E.Clash c) (hf : {q | (c q).isSome}.Finite) (hcov : ¬E.Covered c (E.encode q))
    (hpv : pv (E.encode q) = none) {γ : Type} [MeasurableSpace γ]
    (g : spec.Range q → M → (D →ₒ M).QueryCache → ProbComp γ) :
    𝒟[$ᵗ spec.Range q >>= fun r ↦ ((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
      (simulateQ (D →ₒ M).randomOracle ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run
        z.2 >>= fun w ↦ g r (E.complete q r z.1) (E.byteView (c.cacheQuery q r) w.2)] =
    𝒟[(simulateQ (D →ₒ M).randomOracle
        ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv >>= fun w ↦
      $ᵗ M >>= fun v ↦ g (E.trunc q v) v ((E.byteView c w.2).cacheQuery (E.encode q) v)] := by
  calc _ = 𝒟[$ᵗ spec.Range q >>= fun r ↦ (simulateQ (D →ₒ M).randomOracle
          ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv >>= fun w ↦
            ((D →ₒ M).randomOracle (E.encode q)).run w.2 >>= fun z ↦
              g r (E.complete q r z.1) (E.byteView (c.cacheQuery q r) z.2)] :=
        evalDist_bind_congr_of_support _ _ _ fun r _ ↦
          _root_.randomOracle.evalDist_run_bind_simulateQ_run_swap (E.encode q) _ pv
            fun p _ b ↦ g r (E.complete q r p) (E.byteView (c.cacheQuery q r) b)
    _ = 𝒟[(simulateQ (D →ₒ M).randomOracle
          ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv >>= fun w ↦
            $ᵗ spec.Range q >>= fun r ↦ ((D →ₒ M).randomOracle (E.encode q)).run w.2 >>= fun z ↦
              g r (E.complete q r z.1) (E.byteView (c.cacheQuery q r) z.2)] :=
        OracleComp.evalDist_bind_bind_swap _ _ _
    _ = _ := evalDist_bind_congr_of_support _ _ _ fun w hw ↦ by
        have hwx : w.2 (E.encode q) = none := by
          rw [(apply_of_mem_support_queryAll hw _).2
            (by rwa [mem_map_encode_toList_iff]), hpv]
        simp only [_root_.randomOracle.run_eq, hwx, bind_assoc, pure_bind,
          byteView_cacheQuery_cacheQuery hc hcov]
        exact E.evalDist_bind_complete q fun r v ↦
          g r v ((E.byteView c w.2).cacheQuery (E.encode q) v)

/-- Without a clash and away from the steps that create one, a step of the typed world followed
by the fill has the distribution of the fill followed by the step of the encoded world. -/
private theorem evalDist_typedHashImpl_run_bind_fill {c : spec.QueryCache}
    {pv : (D →ₒ M).QueryCache} (hc : ¬E.Clash c) (hf : {q | (c q).isSome}.Finite)
    (hraw : ∀ x, (pv x).isSome → ∀ q, E.route x = some q → (c q).isSome)
    (u : (spec + (D →ₒ M)).Domain) (hcol : ¬E.Collides c u) {γ : Type} [MeasurableSpace γ]
    (f : (spec + (D →ₒ M)).Range u → (D →ₒ M).QueryCache → ProbComp γ) :
    𝒟[(E.typedHashImpl u).run (c, pv) >>= fun z ↦ E.fill z.2 >>= f z.1] =
      𝒟[E.fill (c, pv) >>= fun b ↦ (E.byteHashImpl u).run b >>= fun z ↦ f z.1 z.2] := by
  have hfill : ∀ pv' : (D →ₒ M).QueryCache, E.fill (c, pv') =
      (fun w ↦ E.byteView c w.2) <$> (simulateQ (D →ₒ M).randomOracle
        ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv' :=
    fun _ ↦ fill_of_not_clash hc hf
  have hpv : ∀ q, (c q) = none → E.route (E.encode q) = some q → pv (E.encode q) = none :=
    fun q hq hr ↦ by
      cases hx : pv (E.encode q) with
      | none => rfl
      | some _ => simpa [hq] using hraw _ (by simp [hx]) q hr
  rcases u with t | x
  · rw [typedHashImpl_inl_run, _root_.randomOracle.run_eq]
    cases hct : c t with
    | some r =>
      simp only [map_pure, pure_bind, hfill, bind_map_left]
      refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 ((apply_of_mem_support_queryAll hw _).1
        ((mem_map_encode_toList_iff hf _).2 ⟨t, rfl, by simp [hct]⟩))
      rw [byteHashImpl_inl_run, _root_.randomOracle.run_eq, byteView_apply_encode hc hct, hp]
      simp [E.trunc_complete]
    | none =>
      have hcov : ¬E.Covered c (E.encode t) := fun h ↦ hcol ⟨hct, h⟩
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (E.isSome_route_encode t)
      have hpvt : pv (E.encode t) = none := by
        cases hx : pv (E.encode t) with
        | none => rfl
        | some _ =>
          have hqs := hraw _ (by simp [hx]) q hq
          exact absurd ⟨q, E.encode_eq_of_route_eq_some hq, hqs⟩ hcov
      simp only [map_bind, map_pure, bind_assoc, pure_bind]
      calc _ = 𝒟[$ᵗ spec.Range t >>= fun r ↦
            ((D →ₒ M).randomOracle (E.encode t)).run pv >>= fun z ↦
              (simulateQ (D →ₒ M).randomOracle
                ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run z.2 >>= fun w ↦
                  f r (E.byteView (c.cacheQuery t r) w.2)] :=
            evalDist_bind_congr_of_support _ _ _ fun r _ ↦
              evalDist_fill_cacheQuery_bind hc hf hcov r (f r)
        _ = _ := evalDist_fresh hc hf hcov hpvt fun r _ b ↦ f r b
        _ = _ := by
          rw [hfill, bind_map_left]
          refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
          have hwx : w.2 (E.encode t) = none := by
            rw [(apply_of_mem_support_queryAll hw _).2
              (by rwa [mem_map_encode_toList_iff]), hpvt]
          rw [byteHashImpl_inl_run, _root_.randomOracle.run_eq,
            byteView_apply_of_not_covered hcov, hwx]
          simp
  · rw [typedHashImpl_inr_run]
    cases hr : E.route x with
    | none =>
      have hcov : ¬E.Covered c x := by
        rintro ⟨q, rfl, _⟩
        simpa [hr] using E.isSome_route_encode q
      simp only [bind_assoc, pure_bind, hfill, bind_map_left]
      rw [_root_.randomOracle.evalDist_run_bind_simulateQ_run_swap x _ pv
        fun p _ b ↦ f p (E.byteView c b)]
      refine evalDist_bind_congr_of_support _ _ _ fun w _ ↦ ?_
      rw [byteHashImpl_inr_run, randomOracle_run_byteView hcov, bind_map_left]
    | some q =>
      obtain rfl := E.encode_eq_of_route_eq_some hr
      dsimp only
      rw [_root_.randomOracle.run_eq (spec₀ := spec) q c]
      cases hcq : c q with
      | some r =>
        simp only [map_pure, bind_assoc, pure_bind, hfill, bind_map_left]
        rw [_root_.randomOracle.evalDist_run_bind_simulateQ_run_swap (E.encode q) _ pv
          fun p _ b ↦ f (E.complete q r p) (E.byteView c b)]
        refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 ((apply_of_mem_support_queryAll hw _).1
          ((mem_map_encode_toList_iff hf _).2 ⟨q, rfl, by simp [hcq]⟩))
        rw [byteHashImpl_inr_run, _root_.randomOracle.run_eq, _root_.randomOracle.run_eq,
          byteView_apply_encode hc hcq, hp]
        simp
      | none =>
        have hcov : ¬E.Covered c (E.encode q) := fun h ↦ hcol ⟨q, hr, hcq, h⟩
        have hpvq := hpv q hcq hr
        simp only [map_bind, map_pure, bind_assoc, pure_bind]
        calc _ = 𝒟[((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
              $ᵗ spec.Range q >>= fun r ↦ (simulateQ (D →ₒ M).randomOracle
                ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run z.2 >>= fun w ↦
                  f (E.complete q r z.1) (E.byteView (c.cacheQuery q r) w.2)] := by
              refine evalDist_bind_congr_of_support _ _ _ fun z hz ↦ ?_
              refine evalDist_bind_congr_of_support _ _ _ fun r _ ↦ ?_
              rw [evalDist_fill_cacheQuery_bind hc hf hcov r,
                QueryImpl.withCaching_run_some _ (QueryImpl.withCaching_run_caches _ _ _ _ hz),
                pure_bind]
          _ = 𝒟[$ᵗ spec.Range q >>= fun r ↦
              ((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
                (simulateQ (D →ₒ M).randomOracle
                  ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run z.2 >>= fun w ↦
                    f (E.complete q r z.1) (E.byteView (c.cacheQuery q r) w.2)] :=
              OracleComp.evalDist_bind_bind_swap _ _ _
          _ = _ := evalDist_fresh hc hf hcov hpvq fun _ v b ↦ f v b
          _ = _ := by
            rw [hfill, bind_map_left]
            refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
            have hwx : w.2 (E.encode q) = none := by
              rw [(apply_of_mem_support_queryAll hw _).2
                (by rwa [mem_map_encode_toList_iff]), hpvq]
            rw [byteHashImpl_inr_run, _root_.randomOracle.run_eq,
              byteView_apply_of_not_covered hcov, hwx]
            simp

omit [DecidableEq D] in
/-- Recording a step keeps every cached typed point cached. -/
theorem isSome_mark {c : spec.QueryCache} {u : (spec + (D →ₒ M)).Domain}
    (a : (spec + (D →ₒ M)).Range u) {q : ι} (hq : (c q).isSome) : (E.mark c u a q).isSome := by
  rcases u with t | x
  · simp [mark, QueryCache.isSome_cacheQuery_apply_iff, hq]
  · simp only [mark]
    cases E.route x <;> simp [QueryCache.isSome_cacheQuery_apply_iff, hq]

omit [DecidableEq D] in
/-- Recording a step that creates a clash, or any step from a state with a clash, leaves a
clash. -/
theorem clash_mark {c : spec.QueryCache} {u : (spec + (D →ₒ M)).Domain}
    (h : E.Clash c ∨ E.Collides c u) (a : (spec + (D →ₒ M)).Range u) :
    E.Clash (E.mark c u a) := by
  rcases h with h | h
  · exact h.mono fun q hq ↦ isSome_mark a hq
  · rcases u with t | x
    · exact clash_cacheQuery_of_covered h.1 h.2 a
    · obtain ⟨q, hr, hq, hcov⟩ := h
      obtain rfl := E.encode_eq_of_route_eq_some hr
      simp only [mark, hr]
      exact clash_cacheQuery_of_covered hq hcov _

omit [DecidableEq D] in
/-- Recording a step keeps finitely many typed points cached. -/
theorem finite_mark {c : spec.QueryCache} (hf : {q | (c q).isSome}.Finite)
    (u : (spec + (D →ₒ M)).Domain) (a : (spec + (D →ₒ M)).Range u) :
    {q | (E.mark c u a q).isSome}.Finite := by
  have hins : ∀ (t : ι) (r : spec.Range t), {q | ((c.cacheQuery t r) q).isSome}.Finite :=
    fun t _ ↦ (hf.insert t).subset fun q hq ↦ by
      simp only [Set.mem_ofPred_eq, QueryCache.isSome_cacheQuery_apply_iff] at hq
      simpa using hq
  rcases u with t | x
  · exact hins t a
  · simp only [mark]
    cases E.route x with
    | some q => exact hins q _
    | none => exact hf

/-- A step of the typed world extends the typed cache by at most one point, and a raw input it
tabulates has the typed point it is read as cached. -/
theorem mem_support_typedHashImpl_run {u : (spec + (D →ₒ M)).Domain}
    {s : spec.QueryCache × (D →ₒ M).QueryCache}
    {z : (spec + (D →ₒ M)).Range u × (spec.QueryCache × (D →ₒ M).QueryCache)}
    (hz : z ∈ support ((E.typedHashImpl u).run s)) :
    s.1 ≤ z.2.1 ∧ ({q | (s.1 q).isSome}.Finite → {q | (z.2.1 q).isSome}.Finite) ∧
      ∀ x, (z.2.2 x).isSome → (s.2 x).isSome ∨ ∀ q, E.route x = some q → (z.2.1 q).isSome := by
  rcases u with t | x
  · rw [typedHashImpl_inl_run, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨QueryImpl.withCaching_cache_le _ _ _ _ hy, fun hf ↦ (hf.insert t).subset fun q hq ↦
      (QueryImpl.withCaching_run_isSome_apply_iff _ hy q).1 hq |>.symm,
      fun _ hx ↦ .inl hx⟩
  · rw [typedHashImpl_inr_run, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hraw : ∀ x', (y.2 x').isSome → (s.2 x').isSome ∨ x' = x :=
      fun x' hx' ↦ (QueryImpl.withCaching_run_isSome_apply_iff _ hy x').1 hx'
    cases hr : E.route x with
    | none =>
      rw [hr, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨le_rfl, id, fun x' hx' ↦ ?_⟩
      rcases hraw x' hx' with h | rfl
      · exact .inl h
      · exact .inr fun q hq ↦ by simp [hr] at hq
    | some q =>
      rw [hr, support_map] at hz
      obtain ⟨y', hy', rfl⟩ := hz
      refine ⟨QueryImpl.withCaching_cache_le _ _ _ _ hy', fun hf ↦ (hf.insert q).subset
        fun q' hq' ↦ (QueryImpl.withCaching_run_isSome_apply_iff _ hy' q').1 hq' |>.symm,
        fun x' hx' ↦ ?_⟩
      rcases hraw x' hx' with h | rfl
      · exact .inl h
      · refine .inr fun q' hq' ↦ ?_
        rw [hr, Option.some.injEq] at hq'
        subst hq'
        simp [QueryImpl.withCaching_run_caches _ _ _ _ hy']

variable (E)

/-- **The fill intertwines the patched typed world with the encoded world** on the states
satisfying `StateInv`. -/
theorem intertwinesOn_fill_patchedImpl_byteImpl :
    QueryImpl.IntertwinesOn E.StateInv E.fill E.patchedImpl E.byteImpl := by
  rintro u ⟨c, pv⟩ ⟨hf, hraw⟩ γ _ f
  rcases u with n | u
  · simp only [patchedImpl_inl_run, byteImpl_inl_run, bind_map_left]
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  · simp only [patchedImpl, byteImpl, QueryImpl.add_apply_inr, patchedHashImpl, StateT.run_mk]
    by_cases hb : E.Clash c ∨ E.Collides c u
    · have hfc : ∀ a b, E.fill (E.mark c u a, b) = pure b :=
        fun a b ↦ fill_of_clash (s := (E.mark c u a, b)) (clash_mark hb a)
      simp only [hb, ↓reduceIte, bind_assoc, pure_bind, hfc]
      rfl
    · simp only [hb, ↓reduceIte]
      obtain ⟨hc, hcol⟩ := not_or.1 hb
      exact evalDist_typedHashImpl_run_bind_fill hc hf (hraw hc) u hcol f

/-- The patched typed world preserves `StateInv`. -/
theorem preservesInv_patchedImpl_stateInv : QueryImpl.PreservesInv E.patchedImpl E.StateInv := by
  rintro (n | u) ⟨c, pv⟩ ⟨hf, hraw⟩ z hz
  · rw [patchedImpl_inl_run, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact ⟨hf, hraw⟩
  · simp only [patchedImpl, QueryImpl.add_apply_inr, patchedHashImpl, StateT.run_mk] at hz
    by_cases hb : E.Clash c ∨ E.Collides c u
    · simp only [hb, ↓reduceIte, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨_, _, _, _, rfl⟩ := hz
      exact ⟨finite_mark hf u _, fun h ↦ absurd (clash_mark hb _) h⟩
    · simp only [hb, ↓reduceIte] at hz
      obtain ⟨hle, hfin, hnew⟩ := mem_support_typedHashImpl_run hz
      refine ⟨hfin hf, fun _ x hx q hq ↦ ?_⟩
      rcases hnew x hx with h | h
      · exact Option.isSome_of_mem (hle (Option.get_mem (hraw (not_or.1 hb).1 x h q hq)))
      · exact h q hq

/-- The typed world preserves a clash. -/
theorem preservesInv_typedImpl_clash :
    QueryImpl.PreservesInv E.typedImpl fun s ↦ E.Clash s.1 := by
  rintro (n | u) s hs z hz
  · rw [typedImpl_inl_run, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hs
  · simp only [typedImpl, QueryImpl.add_apply_inr] at hz
    have hle := (mem_support_typedHashImpl_run hz).1
    exact hs.mono fun q hq ↦ by
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hq
      simp [hle hr]

/-- The typed world agrees with the patched typed world until a clash. -/
theorem agreeUntilBad_typedImpl_patchedImpl :
    QueryImpl.AgreeUntilBad E.typedImpl E.patchedImpl fun s ↦ E.Clash s.1 := by
  refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad fun u s hs ↦ ?_
  rcases u with n | u
  · exact .inl rfl
  · simp only [typedImpl, patchedImpl, QueryImpl.add_apply_inr, patchedHashImpl, StateT.run_mk]
    by_cases hcol : E.Collides s.1 u
    · refine .inr ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
      · obtain ⟨c, pv⟩ := s
        rcases u with t | x
        · rw [typedHashImpl_inl_run, support_map] at hz
          obtain ⟨y, hy, rfl⟩ := hz
          rw [_root_.randomOracle.run_eq, hcol.1] at hy
          simp only [support_bind, support_uniformSample, support_pure, Set.mem_iUnion,
            Set.mem_singleton_iff] at hy
          obtain ⟨r, _, rfl⟩ := hy
          exact clash_cacheQuery_of_covered hcol.1 hcol.2 r
        · obtain ⟨q, hr, hq, hcov⟩ := hcol
          obtain rfl := E.encode_eq_of_route_eq_some hr
          rw [typedHashImpl_inr_run, mem_support_bind_iff] at hz
          obtain ⟨y, _, hz⟩ := hz
          rw [hr, support_map] at hz
          obtain ⟨y', hy', rfl⟩ := hz
          rw [_root_.randomOracle.run_eq, hq] at hy'
          simp only [support_bind, support_uniformSample, support_pure, Set.mem_iUnion,
            Set.mem_singleton_iff] at hy'
          obtain ⟨r, _, rfl⟩ := hy'
          exact clash_cacheQuery_of_covered hq hcov r
      · simp only [hs, hcol, or_true, ↓reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨_, _, _, _, rfl⟩ := hz
        exact clash_mark (.inr hcol) _
    · exact .inl (by simp [hs, hcol])

/-- **An encoded random oracle until a clash.** Run from empty caches, an event of the output of
a computation against the single encoded random oracle is at most the same event, or a clash of
the final typed cache, against independent typed random oracles with raw inputs routed. -/
theorem prEvent_simulateQ_byteImpl_run_le {α : Type}
    (oa : OracleComp (unifSpec + (spec + (D →ₒ M))) α) (P : α → Prop) :
    Pr{let z ← (simulateQ E.byteImpl oa).run ∅}[P z.1] ≤
      Pr{let z ← (simulateQ E.typedImpl oa).run (∅, ∅)}[P z.1 ∨ E.Clash z.2.1] :=
  (E.intertwinesOn_fill_patchedImpl_byteImpl).prEvent_simulateQ_run_le_or_bad
    E.preservesInv_patchedImpl_stateInv E.agreeUntilBad_typedImpl_patchedImpl
    E.preservesInv_typedImpl_clash oa (∅, ∅)
    ⟨by simp, fun _ x hx ↦ by simp at hx⟩ ∅ E.fill_empty P

/-- **An encoded random oracle until a clash, in the random oracle model.** Run from empty
caches, an event of the output of the encoding of a computation in the random oracle model of the
single oracle is at most the same event, or a clash of the final typed cache, in the typed
world. -/
theorem prEvent_simulateQ_romImpl_encodeImpl_run_le {α : Type}
    (oa : OracleComp (unifSpec + (spec + (D →ₒ M))) α) (P : α → Prop) :
    Pr{let z ← (simulateQ (D →ₒ M).romImpl (simulateQ E.encodeImpl oa)).run ∅}[P z.1] ≤
      Pr{let z ← (simulateQ E.typedImpl oa).run (∅, ∅)}[P z.1 ∨ E.Clash z.2.1] := by
  rw [simulateQ_romImpl_simulateQ_encodeImpl]
  exact E.prEvent_simulateQ_byteImpl_run_le oa P

end intertwining

end RandomOracleEncoding

end OracleComp
