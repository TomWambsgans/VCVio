/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Query redirects and the view of a cache through one

A *redirect* of an oracle signature `spec` is an implementation
`ρ : QueryImpl spec (OracleComp spec)` that answers each query by a program over the same
signature; `simulateQ ρ` rewrites a program by replacing each of its queries with that program.

* **Invisibility under an encoding.** If an implementation answers every redirected query `ρ t`
  as it answers `t` itself, it cannot tell a program from its redirected form
  (`QueryImpl.simulateQ_simulateQ_of_forall_eq`). This is the situation of two typed queries that
  share one encoding in a single underlying oracle, when the redirect sends one to the other.
* **The view of a cache.** `QueryCache.viewBy c ρ` is the cache `c` read through `ρ`: its entry
  at `t` is the partial replay of `ρ t` on `c` (`QueryCache.toPartialImpl`). Reading a program on
  the view is reading the redirected program on `c`
  (`QueryCache.simulateQ_viewBy_toPartialImpl`). The view is monotone in the cache
  (`QueryCache.viewBy_mono`) and agrees with `c` wherever `ρ` passes the query on
  (`QueryCache.viewBy_apply_of_eq_query`), so it extends the part of `c` on which `ρ` is the
  identity (`QueryCache.filter_le_viewBy`, with `QueryCache.filter` the restriction of a cache to
  a set of points).
-/

public section

open OracleComp OracleSpec

universe u v

namespace QueryImpl

variable {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {m : Type u → Type v}
  [Monad m] [LawfulMonad m] {α : Type u}

/-- If `enc'` runs each program `ρ t` as `enc` answers the query `t`, then running a program
rewritten by `ρ` through `enc'` is running the program through `enc`. -/
theorem simulateQ_simulateQ_of_forall_eq {enc : QueryImpl spec m} {enc' : QueryImpl spec' m}
    {ρ : QueryImpl spec (OracleComp spec')} (h : ∀ t, simulateQ enc' (ρ t) = enc t)
    (oa : OracleComp spec α) : simulateQ enc' (simulateQ ρ oa) = simulateQ enc oa := by
  rw [← simulateQ_compose]
  exact congrArg (simulateQ · oa) (funext h)

end QueryImpl

namespace OracleSpec.QueryCache

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- The cache `c` read through the redirect `ρ`: its entry at `t` is the partial replay of `ρ t`
on `c`, unset when that replay reads an unset entry. -/
@[expose] def viewBy (c : spec.QueryCache) (ρ : QueryImpl spec (OracleComp spec)) :
    spec.QueryCache :=
  ofFn (c.toPartialImpl ∘ₛ ρ)

@[simp] lemma viewBy_apply (c : spec.QueryCache) (ρ : QueryImpl spec (OracleComp spec))
    (t : spec.Domain) : c.viewBy ρ t = simulateQ c.toPartialImpl (ρ t) := rfl

/-- Reading a program on the view of `c` through `ρ` is reading the program rewritten by `ρ` on
`c`. -/
theorem simulateQ_viewBy_toPartialImpl (c : spec.QueryCache)
    (ρ : QueryImpl spec (OracleComp spec)) (oa : OracleComp spec α) :
    simulateQ (c.viewBy ρ).toPartialImpl oa = simulateQ c.toPartialImpl (simulateQ ρ oa) :=
  QueryImpl.simulateQ_compose _ _ oa

theorem viewBy_mono {c c' : spec.QueryCache} (h : c ≤ c')
    (ρ : QueryImpl spec (OracleComp spec)) : c.viewBy ρ ≤ c'.viewBy ρ :=
  fun t _ ht => simulateQ_toPartialImpl_mono h (ρ t) ht

/-- At a point that `ρ` passes on unchanged, the view of `c` through `ρ` is the entry of `c`. -/
theorem viewBy_apply_of_eq_query {ρ : QueryImpl spec (OracleComp spec)} {t : spec.Domain}
    (ht : ρ t = query t) (c : spec.QueryCache) : c.viewBy ρ t = c t := by
  rw [viewBy_apply, ht]
  simp

/-- The restriction of `c` to the points satisfying `p`: the entries of `c` there, and no entry
elsewhere. -/
@[expose] def filter (c : spec.QueryCache) (p : spec.Domain → Prop) [DecidablePred p] :
    spec.QueryCache :=
  ofFn fun t => if p t then c t else none

@[simp] lemma filter_apply (c : spec.QueryCache) (p : spec.Domain → Prop) [DecidablePred p]
    (t : spec.Domain) : c.filter p t = if p t then c t else none := rfl

theorem filter_le (c : spec.QueryCache) (p : spec.Domain → Prop) [DecidablePred p] :
    c.filter p ≤ c := fun t u ht => by
  rw [filter_apply] at ht
  split_ifs at ht
  exact ht

/-- A cache below `c` whose entries all lie at points satisfying `p` is below the restriction of
`c` to `p`. -/
theorem le_filter {c₀ c : spec.QueryCache} (h : c₀ ≤ c) {p : spec.Domain → Prop}
    [DecidablePred p] (hp : ∀ t, (c₀ t).isSome → p t) : c₀ ≤ c.filter p := fun t u ht => by
  simpa [hp t (by simp [ht])] using h ht

/-- The view of `c` through `ρ` extends the restriction of `c` to the points that `ρ` passes on
unchanged. -/
theorem filter_le_viewBy (c : spec.QueryCache) {ρ : QueryImpl spec (OracleComp spec)}
    {p : spec.Domain → Prop} [DecidablePred p] (hρ : ∀ t, p t → ρ t = query t) :
    c.filter p ≤ c.viewBy ρ := fun t u ht => by
  rw [filter_apply] at ht
  split_ifs at ht with hp
  rwa [viewBy_apply_of_eq_query (hρ t hp)]

end OracleSpec.QueryCache
