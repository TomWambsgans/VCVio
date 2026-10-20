/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Routed
public import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# An unforgeability adversary followed by a program on its output

`SignatureAlg.UnforgeableAdversary.withPost adv post` runs the adversary `adv` and then, as its own
queries to the ambient oracles, the program `post pk out` on its public key `pk` and its output
`out`; it discards the program's result and outputs `out`. A reduction uses it to make the
adversary perform computations, a verification of its own forgery for instance, whose queries the
experiment then records like any other query of the adversary.

* `SignatureAlg.UnforgeableAdversary.RomQueryBound.withPost`: in the random oracle model the
  budget adds up. If `adv` makes at most `qh` hash and `qs` signing queries and every
  `post pk out` at most `v` hash queries, the adversary followed by `post` makes at most `qh + v`
  hash and `qs` signing queries.
* `SignatureAlg.UnforgeableAdversary.mapOracles_withPost`: reading the oracles of an adversary
  followed by a program reads those of both.
* `SignatureAlg.UnforgeableAdversary.route_withPost`: an adversary on the common interface of
  typed and raw oracles followed by a program of typed queries, holding a router
  (`SignatureAlg.UnforgeableAdversary.route`), is the adversary holding the router followed by the
  program.
-/

public section

open OracleSpec OracleComp

/-- A stateful handler that answers each query by lifting a stateless handler keeps the state and
runs the stateless handler. -/
theorem OracleComp.run_simulateQ_of_apply_eq_liftM {ι ι' σ : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} (X : QueryImpl spec (StateT σ (OracleComp spec')))
    (f : QueryImpl spec (OracleComp spec')) (h : ∀ t, X t = liftM (f t)) {β : Type}
    (P : OracleComp spec β) (s : σ) :
    (simulateQ X P).run s = (fun b => (b, s)) <$> simulateQ f P := by
  obtain rfl : X = f.liftTarget (StateT σ (OracleComp spec')) := funext h
  rw [simulateQ_liftTarget, StateT.run_monadLift, monadLift_self, bind_pure_comp]

namespace SignatureAlg

variable {ι : Type} {M PK SK S : Type}

/-- The adversary that runs `adv` and then the program `post pk out` on its public key `pk` and
its output `out`, as its own queries to the ambient oracles; its output is that of `adv`. -/
@[expose] def UnforgeableAdversary.withPost {spec : OracleSpec ι}
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (adv : UnforgeableAdversary sigAlg)
    {β : Type} (post : PK → M × S → OracleComp spec β) : UnforgeableAdversary sigAlg where
  main pk := do
    let out ← adv.main pk
    let _ ← liftComp (post pk out) (spec + (M →ₒ S))
    pure out

/-- **The budget of an adversary followed by a program.** If `adv` makes at most `qh` hash and
`qs` signing queries and every `post pk out` at most `v` hash queries, then `adv` followed by
`post` makes at most `qh + v` hash and `qs` signing queries. -/
theorem UnforgeableAdversary.RomQueryBound.withPost {hs : OracleSpec ι}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {adv : UnforgeableAdversary sigAlg} {qh qs v : ℕ} (hadv : adv.RomQueryBound qh qs)
    {β : Type} {post : PK → M × S → OracleComp (unifSpec + hs) β}
    (hpost : ∀ pk out, IsQueryBoundP (post pk out) (fun t => t.isRight) v) :
    (adv.withPost post).RomQueryBound (qh + v) qs := by
  intro pk
  obtain ⟨hh, hsq⟩ := hadv pk
  have hhash : ∀ t : (unifSpec + hs).Domain,
      t.isRight ↔ IsHashQuery (hs := hs) (M := M) (S := S) (.inl t) := by
    rintro (n | t) <;> simp [IsHashQuery]
  have hsign : ∀ t : (unifSpec + hs).Domain,
      False ↔ IsSignQuery (hs := hs) (M := M) (S := S) (.inl t) := by
    rintro (n | t) <;> simp [IsSignQuery]
  refine ⟨isQueryBoundP_bind hh fun out _ => ?_, (isQueryBoundP_bind hsq fun out _ => ?_).mono
    (Nat.add_zero qs).le⟩
  · exact (isQueryBoundP_bind ((hpost pk out).liftComp_subSpec hhash)
      fun _ _ => isQueryBoundP_pure _ _ 0).mono (Nat.add_zero v).le
  · exact isQueryBoundP_bind ((isQueryBoundP_false (post pk out) 0).liftComp_subSpec hsign)
      fun _ _ => isQueryBoundP_pure _ _ 0

/-- Reading the oracles of an adversary followed by a program reads those of the adversary and
of the program. -/
theorem UnforgeableAdversary.mapOracles_withPost {ι' : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} {SK' : Type} (G : QueryImpl spec (OracleComp spec'))
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    {sigAlg' : SignatureAlg (OracleComp spec') M PK SK' S} (adv : UnforgeableAdversary sigAlg)
    {β : Type} (post : PK → M × S → OracleComp spec β) :
    (adv.withPost post).mapOracles G (sigAlg' := sigAlg') =
      (adv.mapOracles G (sigAlg' := sigAlg')).withPost fun pk out => simulateQ G (post pk out) := by
  refine congrArg UnforgeableAdversary.mk (funext fun pk => ?_)
  simp only [UnforgeableAdversary.mapOracles_main, UnforgeableAdversary.withPost, simulateQ_bind,
    simulateQ_pure]
  refine bind_congr fun out => ?_
  congr 1
  rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget]
  rfl

/-- **Routing an adversary followed by a typed program.** An adversary on the common interface
`unifSpec + (hs + ext)` followed by a program of queries to `unifSpec + hs`, holding the router
`R`, is the adversary holding `R`, followed by the program. -/
theorem UnforgeableAdversary.route_withPost {ιe : Type} {hs : OracleSpec ι} {ext : OracleSpec ιe}
    {SK' σ : Type} {sigAlg' : SignatureAlg (OracleComp (unifSpec + (hs + ext))) M PK SK' S}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (R : PK → QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))) (s₀ : σ)
    (adv : UnforgeableAdversary sigAlg') {β : Type}
    (post : PK → M × S → OracleComp (unifSpec + hs) β) :
    (adv.withPost fun pk out => simulateQ (liftTypedImpl (ext := ext)) (post pk out)).route
        (sigAlg := sigAlg) R s₀ =
      (adv.route (sigAlg := sigAlg) R s₀).withPost post := by
  simp only [UnforgeableAdversary.route, UnforgeableAdversary.withPost]
  congr 1
  funext pk
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, simulateQ_pure, map_bind,
    bind_map_left, StateT.run_pure]
  refine bind_congr fun a => ?_
  rw [liftComp_def, liftComp_def, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    OracleComp.run_simulateQ_of_apply_eq_liftM _ (fun t => (liftM ((unifSpec + hs).query t) :
      OracleComp ((unifSpec + hs) + (M →ₒ S)) _)) fun t => by rcases t with n | t <;> rfl]
  simp only [map_pure, bind_pure_comp, Functor.map_map]
  congr 2
  funext t
  rcases t with n | t <;> rfl

end SignatureAlg
