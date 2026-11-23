import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

noncomputable section

namespace GlobalTheory.LocM.Cht.GoodOfZero

section Fibre

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem isProper_thick {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) [Subsingleton D.X] :
    IsProper (pullback.snd G.hom (thick R I e)) := by
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hp := g.isKernel
  have : Mono g.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := GlobalTheory.UU.point_eq_of_subsingleton _ _
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono g.q.left := inferInstanceAs (Mono ((Over.forget _).map g.q))
  have : EffectiveEpi g.q.left := inferInstance
  have : IsIso g.q.left := isIso_of_mono_of_strongEpi _
  have := D.P.isAb.proper
  have : IsProper (thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  change IsProper (thickObj R I e G).hom
  rw [← Over.w g.q]
  infer_instance

theorem closedPoint_mem_abLocus {R : Type} [CommRing R] [IsLocalRing R] {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    (h : IsProper (pullback.snd G.hom (thick R (maximalIdeal R) e))) : closedPoint R ∈ abLocus G := by
  rintro K _ _ t ⟨q, hq⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective t
  have hk : ∀ a ∈ maximalIdeal R ^ (e + 1), φ.hom a = 0 := fun a ha => by
    have h1 : a ∈ maximalIdeal R := Ideal.pow_le_self (Nat.succ_ne_zero e) ha
    have h2 : Ideal.comap φ.hom q.asIdeal = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hq
    rw [← h2, show q.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ q.2] at h1
    exact h1
  let u : Sp K ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ φ.hom hk))
  have hu : u ≫ thick R (maximalIdeal R) e = Spec.map φ := by
    rw [← Spec.map_comp]; rfl
  have hp := (IsPullback.of_hasPullback (pullback.snd G.hom (thick R (maximalIdeal R) e)) u).paste_horiz
    (IsPullback.of_hasPullback G.hom (thick R (maximalIdeal R) e))
  rw [← hu, ← hp.isoPullback_inv_snd]
  infer_instance

end Fibre

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

theorem abOfTriv : GlobalTheory.LocM.Cht.AbOfTrivSt := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P A _ hs
  have hloc : IsLocalHom A.f := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((mem_maximalIdeal_ball (A.f a)).2 (A.f_loc a ((mem_maximalIdeal _).2 h))) ha⟩
  have e1 : spMap A.f (closedPoint _) = closedPoint A.R := comap_closedPoint A.f
  have e2 : P.yt (closedPoint ↥(intO ↥C.S)) = A.ι (closedPoint A.R) := by
    rw [← A.fac]
    exact congrArg A.ι e1
  rw [e2]
  exact (abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 _).2
    (closedPoint_mem_abLocus (isProper_thick (A.U.U.toUnifPre.gt 0)))

end GlobalTheory.LocM.Cht.GoodOfZero
