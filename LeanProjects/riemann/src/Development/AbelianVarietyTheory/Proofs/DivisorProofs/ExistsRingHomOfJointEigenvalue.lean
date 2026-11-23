import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

open Matrix

theorem jointEigen_ringHom_toIntegers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (hv : v.Integers O)
    (ρ : Λ →+* Matrix (Fin h) (Fin h) O) (χ : Λ → C)
    (hne : (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) ≠ ⊥) :
    ∃ σ : Λ →+* O, ∀ a, algebraMap O C (σ a) = χ a := by
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  set ψ : Λ →+* Matrix (Fin h) (Fin h) C := (algebraMap O C).mapMatrix.comp ρ with hψ
  have hψa : ∀ a, (ρ a).map (algebraMap O C) = ψ a := fun a => rfl
  have hE : ∀ a, ψ a *ᵥ x = χ a • x := by
    intro a
    have := (Submodule.mem_iInf _).1 hxmem a
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hψa] at this
    exact this
  have canc : ∀ c d : C, c • x = d • x → c = d := fun c d hcd => smul_left_injective C hx0 hcd
  have h1 : χ 1 = 1 := canc _ _ (by rw [← hE, map_one, Matrix.one_mulVec, one_smul])
  have hadd : ∀ a b, χ (a + b) = χ a + χ b := fun a b =>
    canc _ _ (by rw [← hE, map_add, Matrix.add_mulVec, hE, hE, add_smul])
  have hmul : ∀ a b, χ (a * b) = χ a * χ b := fun a b =>
    canc _ _ (by rw [← hE, map_mul, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul, hE, smul_smul, mul_comm])
  have h0 : χ 0 = 0 := canc _ _ (by rw [← hE, map_zero, Matrix.zero_mulVec, zero_smul])

  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx0 (funext hcon)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v (x j)) ⟨i0, Finset.mem_univ _⟩
  have hvi : v (x i) ≠ 0 := by
    intro h'
    have := hi i0 (Finset.mem_univ _)
    rw [h'] at this
    exact hi0 ((Valuation.zero_iff v).1 (le_antisymm this (zero_le')))
  have hint : ∀ a, v (χ a) ≤ 1 := by
    intro a
    have hrow : χ a * x i = ∑ j, ψ a i j * x j := by
      have := congrFun (hE a) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]; rfl
    have hle : v (χ a * x i) ≤ v (x i) := by
      rw [hrow]
      apply Valuation.map_sum_le
      intro j _
      rw [map_mul]
      calc v (ψ a i j) * v (x j) ≤ 1 * v (x i) := by
            apply mul_le_mul' _ (hi j (Finset.mem_univ _))
            exact hv.map_le_one _
        _ = v (x i) := one_mul _
    rw [map_mul] at hle
    have hpos : 0 < v (x i) := lt_of_le_of_ne (zero_le') (Ne.symm hvi)
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos
  choose σf hσf using fun a => hv.exists_of_le_one (hint a)
  refine ⟨{ toFun := σf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσf⟩
  · exact hv.hom_inj (by rw [hσf, h1, map_one])
  · intro a b; exact hv.hom_inj (by rw [hσf, map_mul, hσf, hσf, hmul])
  · exact hv.hom_inj (by rw [hσf, h0, map_zero])
  · intro a b; exact hv.hom_inj (by rw [hσf, map_add, hσf, hσf, hadd])

end GlobalTheory
