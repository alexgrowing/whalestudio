import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset
import Development.WeilBound.CoreStatements.IdealCycleValues.IntersectionNumbersPermInvariant
import Development.WeilBound.CoreStatements.IdealCycleValues.IntNumLCons

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_linear_change_classes : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime V → ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → genNum F V (fun t => ∑ i, M t i • cls i) H Q = genNum F V cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  intro F _ K _ _ ι _ V d hV hd σ σ' _ cls M H m hH Q hQ
  unfold genNum classList
  rw [BaseChangeColon.evL_eq (H := aeval _ H)]
  exact BaseChangeColon.subst_abs d (fun l => (intNumL F V l : ℝ))
    (fun l l' h => by rw [BaseChangeColon.intersection_numbers_perm_invariant.1 F K ι V l l' h])
    (fun b b' l hl => by
      rw [BaseChangeColon.intNumL_add F K ι V d hV hd b b' l hl, Int.cast_add]) cls M H m hH Q hQ
