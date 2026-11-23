import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore

open Finset Matrix

open scoped ComplexConjugate

noncomputable section

open Classical

namespace Formalism.L2.SG.NormCut.PsiNatEquivPf

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

def IsUTm (A : Matrix (Fin k) (Fin k) F) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

theorem IsUTm.mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) : IsUTm (A * B) := by
  obtain ⟨hA1, hA0⟩ := hA
  obtain ⟨hB1, hB0⟩ := hB
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA1, hB1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA0 i l h, zero_mul]
      · rw [hB0 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hA0 i l h, zero_mul]
    · rw [hB0 l j (lt_of_lt_of_le hij h), mul_zero]

theorem superdiag_mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) :
    superdiag k (A * B) = superdiag k A + superdiag k B := by
  obtain ⟨hA1, hA0⟩ := hA
  obtain ⟨hB1, hB0⟩ := hB

  have key : ∀ i j : Fin k, (j : ℕ) = (i : ℕ) + 1 → (A * B) i j = A i j + B i j := by
    intro i j hij
    have hij' : i < j := by
      rw [Fin.lt_iff_val_lt_val]
      omega
    rw [Matrix.mul_apply, Finset.sum_eq_add i j (ne_of_lt hij')]
    · rw [hA1 i, hB1 j, one_mul, mul_one, add_comm]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc.1 with h | h
      · rw [hA0 i c h, zero_mul]
      · have h' : j < c := by
          have h1 : (i : ℕ) < c := h
          have h2 : (c : ℕ) ≠ j := fun e => hc.2 (Fin.ext e)
          rw [Fin.lt_iff_val_lt_val]
          omega
        rw [hB0 c j h', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [superdiag]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · exact key i j h
  · rw [add_zero]

theorem IsUTm.inv_val (u : GL (Fin k) F) (h : IsUTm (u : Matrix (Fin k) (Fin k) F)) :
    IsUTm ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) := by
  have htri : ∀ i j : Fin k, j < i → ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) i j = 0 := by
    intro i j hij
    letI : Invertible (u : Matrix (Fin k) (Fin k) F) := u.invertible
    have hb : (u : Matrix (Fin k) (Fin k) F).BlockTriangular id := by
      intro a b hab
      exact h.2 a b hab
    rw [Matrix.coe_units_inv u]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb hij
  refine ⟨fun i => ?_, htri⟩

  have hmul : ((u : Matrix (Fin k) (Fin k) F) * ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)) i i = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i, h.1 i, one_mul] at hmul
  · exact hmul
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl' | hl'
    · rw [h.2 i l hl', zero_mul]
    · rw [htri l i hl', mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem isUni_mul {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) : IsUni k (x * y) := by
  have h := IsUTm.mul (A := (x : Matrix (Fin k) (Fin k) F)) (B := (y : Matrix (Fin k) (Fin k) F)) hx hy
  show IsUTm ((x * y : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)
  rw [Units.val_mul]
  exact h

theorem isUni_inv {x : GL (Fin k) F} (hx : IsUni k x) : IsUni k x⁻¹ := IsUTm.inv_val x hx

theorem psiU_mul (ψ₀ : AddChar F ℂ) {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) :
    psiU ψ₀ (x * y) = psiU ψ₀ x * psiU ψ₀ y := by
  unfold psiU
  rw [Units.val_mul, superdiag_mul (A := (x : Matrix (Fin k) (Fin k) F))
    (B := (y : Matrix (Fin k) (Fin k) F)) hx hy]
  first
    | exact AddChar.map_add_eq_mul ψ₀ _ _
    | exact AddChar.map_add_mul ψ₀ _ _

theorem norm_addChar (ψ₀ : AddChar F ℂ) (a : F) : ‖ψ₀ a‖ = 1 := by

  have hpow : ψ₀ a ^ Fintype.card F = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  have hn : Fintype.card F ≠ 0 := Fintype.card_ne_zero
  have h2 : ‖ψ₀ a‖ ^ Fintype.card F = 1 := by
    rw [← norm_pow, hpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h2

end Formalism.L2.SG.NormCut.PsiNatEquivPf

open Formalism.L2.SG.GGMirabolic Formalism.L2.SG.NormCut.PsiNatEquivPf in
theorem Formalism.L2.SG.NormCut.psi_natural_equiv_holds : Formalism.L2.SG.NormCut.PsiNatEquiv := by
  intro F _ _ k ψ₀ x w hw
  refine ⟨?_, ?_, ?_⟩
  · by_cases hx : IsUni k x
    · unfold psiNat
      rw [if_pos (isUni_mul hx hw), if_pos hx, if_pos hw]
      exact psiU_mul ψ₀ hx hw
    · have hxw : ¬ IsUni k (x * w) := by
        intro h
        have h' := isUni_mul h (isUni_inv hw)
        rw [mul_inv_cancel_right] at h'
        exact hx h'
      unfold psiNat
      rw [if_neg hxw, if_neg hx, zero_mul]
  · by_cases hx : IsUni k x
    · unfold psiNat
      rw [if_pos (isUni_mul hw hx), if_pos hx, if_pos hw]
      exact psiU_mul ψ₀ hw hx
    · have hwx : ¬ IsUni k (w * x) := by
        intro h
        have h' := isUni_mul (isUni_inv hw) h
        rw [inv_mul_cancel_left] at h'
        exact hx h'
      unfold psiNat
      rw [if_neg hwx, if_neg hx, mul_zero]
  · unfold psiNat psiU
    rw [if_pos hw]
    first
      | (rw [Complex.conj_mul', norm_addChar]; simp)
      | (rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar]; simp)
