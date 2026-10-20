/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Reading a cache through a query redirect

A *redirect* of an oracle signature `spec` into `spec'` is an implementation
`ρ : QueryImpl spec (OracleComp spec')` that answers each query by a program over `spec'`;
`simulateQ ρ` rewrites a program by replacing each of its queries with that program. When
`spec' = spec` and an implementation answers every `ρ t` as it answers `t` itself, it cannot tell a
program from its redirected form (`QueryImpl.simulateQ_simulateQ_eq_of_apply`): this is the
situation of two typed queries that share one encoding in a single underlying oracle, when the
redirect sends one to the other.

`QueryCache.viewBy c ρ` is a cache `c` of `spec'` read through `ρ`: its entry at `t` is the
partial replay of `ρ t` on `c` (`QueryCache.toPartialImpl`). Reading a program on the view is
reading the redirected program on `c` (`QueryCache.simulateQ_viewBy_toPartialImpl`), and the view
is monotone in the cache (`QueryCache.viewBy_mono`). For a redirect of `spec` into itself, the
view agrees with `c` wherever `ρ` passes the query on (`QueryCache.viewBy_apply_of_eq_query`), so
it extends the restriction `QueryCache.filter p c` of `c` to any set `p` of such points
(`QueryCache.filter_le_viewBy`).
-/

public section

open OracleComp OracleSpec

universe u v

namespace OracleSpec.QueryCache

section Filter

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- The restriction of `c` to the points satisfying `p`: the entries of `c` there, and no entry
elsewhere. -/
@[expose] def filter (p : spec.Domain → Prop) [DecidablePred p] (c : spec.QueryCache) :
    spec.QueryCache :=
  ofFn fun t => if p t then c t else none

/-- The entry of `filter p c` at `t` is that of `c` when `p t` holds and unset otherwise. -/
@[simp] lemma filter_apply (p : spec.Domain → Prop) [DecidablePred p] (c : spec.QueryCache)
    (t : spec.Domain) : filter p c t = if p t then c t else none := rfl

/-- The restriction of a cache lies below the cache. -/
theorem filter_le (p : spec.Domain → Prop) [DecidablePred p] (c : spec.QueryCache) :
    filter p c ≤ c := fun t u ht => by
  rw [filter_apply] at ht
  split_ifs at ht
  exact ht

/-- A cache below `c` whose entries all lie at points satisfying `p` is below the restriction of
`c` to `p`. -/
theorem le_filter {c₀ c : spec.QueryCache} (h : c₀ ≤ c) {p : spec.Domain → Prop}
    [DecidablePred p] (hp : ∀ t, (c₀ t).isSome → p t) : c₀ ≤ filter p c := fun t u ht => by
  simpa [hp t (by simp [ht])] using h ht

end Filter

section ViewBy

variable {ι ι' : Type u} {spec : OracleSpec.{u, u} ι} {spec' : OracleSpec.{u, u} ι'}
  {α : Type u}

/-- The cache `c` of `spec'` read through the redirect `ρ`: its entry at `t` is the partial
replay of `ρ t` on `c`, unset when that replay reads an unset entry. -/
@[expose] def viewBy (c : spec'.QueryCache) (ρ : QueryImpl spec (OracleComp spec')) :
    spec.QueryCache :=
  ofFn (c.toPartialImpl ∘ₛ ρ)

/-- The entry of the view at `t` is the partial replay of `ρ t` on the cache. -/
@[simp] lemma viewBy_apply (c : spec'.QueryCache) (ρ : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) : c.viewBy ρ t = simulateQ c.toPartialImpl (ρ t) := rfl

/-- Reading a program on the view of `c` through `ρ` is reading the program rewritten by `ρ` on
`c`. -/
theorem simulateQ_viewBy_toPartialImpl (c : spec'.QueryCache)
    (ρ : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α) :
    simulateQ (c.viewBy ρ).toPartialImpl oa = simulateQ c.toPartialImpl (simulateQ ρ oa) :=
  QueryImpl.simulateQ_compose _ _ oa

/-- The view through a fixed redirect is monotone in the cache. -/
theorem viewBy_mono {c c' : spec'.QueryCache} (h : c ≤ c')
    (ρ : QueryImpl spec (OracleComp spec')) : c.viewBy ρ ≤ c'.viewBy ρ :=
  fun t _ ht => simulateQ_toPartialImpl_mono h (ρ t) ht

/-- At a point that `ρ` passes on unchanged, the view of `c` through `ρ` is the entry of `c`. -/
theorem viewBy_apply_of_eq_query {ρ : QueryImpl spec (OracleComp spec)} {t : spec.Domain}
    (ht : ρ t = query t) (c : spec.QueryCache) : c.viewBy ρ t = c t := by
  rw [viewBy_apply, ht]
  simp

/-- The view of `c` through `ρ` extends the restriction of `c` to points that `ρ` passes on
unchanged. -/
theorem filter_le_viewBy (c : spec.QueryCache) {ρ : QueryImpl spec (OracleComp spec)}
    {p : spec.Domain → Prop} [DecidablePred p] (hρ : ∀ t, p t → ρ t = query t) :
    filter p c ≤ c.viewBy ρ := fun t u ht => by
  rw [filter_apply] at ht
  split_ifs at ht with hp
  rwa [viewBy_apply_of_eq_query (hρ t hp)]

end ViewBy

end OracleSpec.QueryCache
