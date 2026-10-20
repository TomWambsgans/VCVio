/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Redirect

/-!
# A redirect that moves a query

The oracle is a random oracle on `Bool`. The redirect `toFalse` answers every query at the point
`false`, so it moves the query at `true` and passes the query at `false` on unchanged.

* The redirect changes a program: on the cache holding only the point `false`, the query at
  `true` fails to replay, while its redirected form succeeds. So the view of that cache through
  `toFalse` differs from the cache, and the replay identity relates two different readings.
* The view holds an entry at `true` that the cache lacks, while it still extends the cache
  restricted to `false`, the point the redirect passes on.
* An encoding that sends both points to one underlying query cannot see the redirect, although
  the redirect changes the program.
-/

public section

open OracleComp OracleSpec

namespace RedirectToy

/-- A random oracle on `Bool`. -/
abbrev spec := Bool →ₒ Bool

/-- Answer every query at the point `false`. -/
def toFalse : QueryImpl spec (OracleComp spec) := fun _ => spec.query false

/-- The cache holding the answer `b` at `false` and nothing at `true`. -/
def cacheAt (b : Bool) : spec.QueryCache := (∅ : spec.QueryCache).cacheQuery false b

theorem simulateQ_cacheAt_query_true (b : Bool) :
    simulateQ (cacheAt b).toPartialImpl (spec.query true : OracleComp spec Bool) = none := by
  simp [cacheAt, QueryCache.cacheQuery_of_ne]

theorem simulateQ_viewBy_cacheAt_query_true (b : Bool) :
    simulateQ ((cacheAt b).viewBy toFalse).toPartialImpl
      (spec.query true : OracleComp spec Bool) = some b := by
  rw [QueryCache.simulateQ_viewBy_toPartialImpl]
  simp [toFalse, cacheAt]

/-- The redirect changes the program. -/
theorem simulateQ_toFalse_ne (b : Bool) :
    simulateQ toFalse (spec.query true : OracleComp spec Bool) ≠ spec.query true := by
  intro h
  have := simulateQ_viewBy_cacheAt_query_true b
  rw [QueryCache.simulateQ_viewBy_toPartialImpl, h, simulateQ_cacheAt_query_true] at this
  exact Option.some_ne_none b this.symm

theorem viewBy_cacheAt_ne (b : Bool) : (cacheAt b).viewBy toFalse ≠ cacheAt b := fun h => by
  have := simulateQ_viewBy_cacheAt_query_true b
  rw [h, simulateQ_cacheAt_query_true] at this
  exact Option.some_ne_none b this.symm

theorem filter_cacheAt_le_viewBy (b : Bool) :
    (cacheAt b).filter (· = false) ≤ (cacheAt b).viewBy toFalse :=
  QueryCache.filter_le_viewBy _ fun t ht => by subst ht; rfl

/-- One underlying query answering both points of `spec`. -/
abbrev single := Unit →ₒ Bool

/-- Send every point of `spec` to the one point of `single`. -/
def collapse : QueryImpl spec (OracleComp single) := fun _ => single.query ()

/-- The collapsing encoding cannot see the redirect. -/
theorem simulateQ_collapse_simulateQ_toFalse {α : Type} (oa : OracleComp spec α) :
    simulateQ collapse (simulateQ toFalse oa) = simulateQ collapse oa :=
  QueryImpl.simulateQ_simulateQ_of_forall_eq (fun _ => by simp [toFalse, collapse]) oa

end RedirectToy
