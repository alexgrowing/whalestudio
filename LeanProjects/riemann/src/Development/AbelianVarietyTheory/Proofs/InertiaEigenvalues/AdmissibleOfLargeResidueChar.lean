import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKatoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDescentEnlargementCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCocycleDescentEnlargementStatement

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc
open Module

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), tableLineDegreeTwo.aux₃ D HW F → tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ), ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) → ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) := by
  intro D HW F i r ρ π hconds hadm20 hJa hGood hπ hG2 hG3 hCont hDec hEps h5 hsm hq hd hposition w hw
  obtain ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, hS⟩ :=
    GlobalTheory.T.exists_exactLocalConditionData_at_place D HW F i r ρ π hadm20 hJa hGood hπ hG2 hG3 hCont hDec hEps h5 hsm hq hd hposition w hw
  have hTop : tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) :=
    hconds (D.nd.l i) (D.nbr i w hw).Kw C.LL hA lam hlam
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.unramifiedEnlargement_cut_cocycles_blochKato D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hS hGood hπ hDec hCont
  refine ⟨?_, ?_, ?_⟩
  · have hsub : ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
        z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (WpO D.nd i ρ π)) :=
      fun z hz => GlobalTheory.T.mem_finite_part_of_lift D i w hw C D.R.r _ z (h1 z hz)
    have hle := Submodule.span_le.2 hsub
    unfold LocBound lenModN
    have h0 : Module.length (Br.OLL D.nbr i w hw)
        (↥(Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Set.univ (WpO D.nd i ρ π))) ⧸
          (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (WpO D.nd i ρ π))).comap
            (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Set.univ (WpO D.nd i ρ π))).subtype) = 0 := by
      rw [Module.length_eq_zero_iff, Submodule.comap_subtype_eq_top.2 hle]
      refine ⟨fun a b => ?_⟩
      induction a using Submodule.Quotient.induction_on
      induction b using Submodule.Quotient.induction_on
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top
    rw [h0]
    exact zero_le
  · intro c hc z hz
    exact GlobalTheory.T.coboundary_descent_enlargement_coefficients D i w hw C 1 _ z (h2 c hc z hz)
  · intro z hz
    have := GlobalTheory.T.unramifiedCocycle_descent_enlargement D i w hw C 1 _ _ z (h3 z hz)
    rwa [← GlobalTheory.BridgeInertia.inertEq D i w hw] at this

end GlobalTheory.UseLoc
