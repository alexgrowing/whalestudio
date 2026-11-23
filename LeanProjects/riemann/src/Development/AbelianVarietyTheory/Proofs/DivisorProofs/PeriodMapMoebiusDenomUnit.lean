import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.SiegelAction

theorem den_isUnit_of_isPeriodMap : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B (fun b => moeb γ (τ b)) → ∀ b ∈ B, IsUnit (den γ (τ b)) := by
  intro E _ _ g B τ γ hP b hb
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact isUnit_of_subsingleton _
  by_contra h
  have hdet : ¬ IsUnit (den γ (τ b)).det := fun hd => h ((Matrix.isUnit_iff_isUnit_det _).2 hd)
  have hinv : (den γ (τ b))⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hdet
  have hS : GlobalTheory.IsSiegel (moeb γ (τ b)) := hP.2.2 b hb
  have h0 : moeb γ (τ b) = 0 := by simp [moeb, hinv]
  rw [h0] at hS
  have hpd := hS.2
  let i : Fin g := ⟨0, hg⟩
  have hx : (Finsupp.single i (1 : ℝ)) ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  have := hpd.2 hx
  simp at this

end GlobalTheory.SiegelAction
