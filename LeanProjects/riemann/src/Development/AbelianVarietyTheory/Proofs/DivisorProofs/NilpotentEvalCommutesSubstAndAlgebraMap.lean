import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentXStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem evA_subst_and_map : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], (∀ (τ : Type) [Finite τ] (φ : MvPowerSeries τ k →ₐ[k] A), (∀ t, IsNilpotent (φ (X t))) → ∀ a : σ → MvPowerSeries τ k, (∀ i, constantCoeff (a i) = 0) → ∀ (y : σ → A) (hy : ∀ i, IsNilpotent (y i)), (∀ i, φ (a i) = y i) → ∀ f : MvPowerSeries σ k, φ (subst a f) = evA k y hy f) ∧ ∀ (B : Type) [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : σ → B) (hy : ∀ i, IsNilpotent (y i)), (∀ i, g (x i) = y i) → ∀ f : MvPowerSeries σ k, g (evA k x hx f) = evA k y hy f := by
  intro k _ σ _ A _ _
  refine ⟨?_, ?_⟩
  · intro τ _ φ _ a ha y hy hφa f
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have key : evA k y hy = φ.comp (substAlgHom hs) := by
      refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ A _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i, AlgHom.comp_apply, coe_substAlgHom, subst_X hs, hφa]
    rw [key, AlgHom.comp_apply, coe_substAlgHom]
  · intro B _ _ g x hx y hy hg f
    have key : evA k y hy = g.comp (evA k x hx) := by
      refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ B _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i, AlgHom.comp_apply, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hg]
    rw [key, AlgHom.comp_apply]

end GlobalTheory
