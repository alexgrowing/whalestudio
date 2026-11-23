import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.SupThetaGrowth

theorem om_sup_quotHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  intro D ψ S T χS χT om hom f hf
  obtain ⟨C, A, hC⟩ := om_sup_growth D ψ S T χS χT om hom f hf
  refine ⟨max C 0 * 4 ^ A, A, fun g h w => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  have e := om_rat_mul D ψ S T χS χT om hom f hf γ⁻¹ (inv_mem hγ) γ'⁻¹ (inv_mem hγ') (γ * g) (γ' * h) w
  rw [inv_mul_cancel_left, inv_mul_cancel_left] at e
  rw [e]
  have p1 := (height_pos S (γ * g)).le
  have p2 := (height_pos T (γ' * h)).le
  have q1 := (quotHeight_pos S g).le
  calc _ ≤ C * (height S (γ * g) * height T (γ' * h)) ^ A := hC _ _ _
    _ ≤ max C 0 * (height S (γ * g) * height T (γ' * h)) ^ A :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (mul_nonneg p1 p2) A)
    _ ≤ max C 0 * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg p1 p2)
          (mul_le_mul h1 h2 p2 (mul_nonneg zero_le_two q1)) A) (le_max_right _ _)
    _ = max C 0 * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A := by
        generalize quotHeight S g = a
        generalize quotHeight T h = b
        rw [show 2 * a * (2 * b) = 4 * (a * b) by ring, mul_pow, mul_assoc]

end GlobalTheory.SupThetaGrowth
