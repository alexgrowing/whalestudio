import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_rename_variables : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) := by
  refine ⟨?_, ?_⟩
  · intro O _ _ _ K _ _ ι _ σ σ' e Z cls H Q
    unfold cycNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
  · intro F _ K _ _ ι _ σ σ' e V cls H Q
    unfold genNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
