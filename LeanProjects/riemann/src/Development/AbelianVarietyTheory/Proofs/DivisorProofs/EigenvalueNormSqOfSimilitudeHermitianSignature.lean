import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.EigenvalueNormSignature

theorem form_mulVec {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star (M *ᵥ x) ⬝ᵥ A *ᵥ (M *ᵥ y) = star x ⬝ᵥ (Mᴴ * A * M) *ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_ne_zero_of_sig {n : ℕ} {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (hs : sigPosH hh + sigNegH hh = n) : h.det ≠ 0 := by
  intro hd
  rw [hh.det_eq_prod_eigenvalues] at hd
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hd
  have hi0 : hh.eigenvalues i = 0 := by simpa using hi
  unfold sigPosH sigNegH at hs
  have hdis : Disjoint (fun j : Fin n => 0 < hh.eigenvalues j) (fun j => hh.eigenvalues j < 0) := by
    rw [Pi.disjoint_iff]; intro j
    simp only [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩; linarith
  rw [← Fintype.card_subtype_or_disjoint _ _ hdis] at hs
  have hlt : Fintype.card {j : Fin n // 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0} < Fintype.card (Fin n) :=
    Fintype.card_subtype_lt (p := fun j => 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0) (x := i)
      (by rw [hi0]; simp)
  rw [Fintype.card_fin] at hlt
  omega

end GlobalTheory.EigenvalueNormSignature

namespace GlobalTheory

open GlobalTheory.EigenvalueNormSignature in

theorem eig_norm_sq_of_similitude : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  intro n h Q Γ hh Z c hle hs hQ hc hΓ hcase w x hx hw
  have hdet := det_ne_zero_of_sig hh hs
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hZinj : ∀ v : Fin n → ℂ, v ≠ 0 → Zm *ᵥ v ≠ 0 := by
    intro v hv h0
    apply hv
    have : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ (Zm *ᵥ v) = v := by
      rw [mulVec_mulVec, hZm, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hB : ∀ u v : Fin n → ℂ, star u ⬝ᵥ Q *ᵥ v = star (Zm *ᵥ u) ⬝ᵥ h *ᵥ (Zm *ᵥ v) := by
    intro u v; rw [form_mulVec, hQ]

  have hsim : ∀ (a b : ℂ) (u v : Fin n → ℂ), Γ *ᵥ u = a • u → Γ *ᵥ v = b • v →
      (star a * b - c) * (star u ⬝ᵥ Q *ᵥ v) = 0 := by
    intro a b u v hu hv
    have e := form_mulVec Γ Q u v
    rw [hΓ, hu, hv] at e
    simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_mulVec] at e
    rw [RCLike.star_def] at e ⊢
    linear_combination e
  have hnorm : ∀ a : ℂ, star a * a = (c : ℂ) → ‖a‖ ^ 2 = c := by
    intro a ha
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = c := by
      rw [← ha, RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this
  by_cases hq : star x ⬝ᵥ Q *ᵥ x = 0
  · rcases hcase with h0 | ⟨μ, x₀, hμ, hpos⟩
    · have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x) (hZinj x hx)
      rw [← hB, hq] at this; simp at this
    · have h1 : sigPosH hh = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · have hx₀ : x₀ ≠ 0 := by rintro rfl; simp at hpos
          have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x₀) (hZinj x₀ hx₀)
          rw [← hB] at this; linarith
        · exact h1
      have hμμ := hsim μ μ x₀ x₀ hμ hμ
      have hq0 : star x₀ ⬝ᵥ Q *ᵥ x₀ ≠ 0 := fun e => by rw [e] at hpos; simp at hpos
      have hμc : star μ * μ = (c : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hμμ).resolve_right hq0)
      by_cases hb : star x₀ ⬝ᵥ Q *ᵥ x = 0
      · have := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet h1 (Zm *ᵥ x₀) (Zm *ᵥ x)
          (by rw [← hB]; exact hpos) (by rw [← hB]; exact hb) (hZinj x hx)
        rw [← hB, hq] at this; simp at this
      · have hμw := sub_eq_zero.mp ((mul_eq_zero.mp (hsim μ w x₀ x hμ hw)).resolve_right hb)
        have hμ0 : star μ ≠ 0 := by
          intro e; rw [e, zero_mul] at hμc; exact hc (by exact_mod_cast hμc.symm)
        have hwμ : w = μ := mul_left_cancel₀ hμ0 (hμw.trans hμc.symm)
        rw [hwμ]; exact hnorm μ hμc
  · exact hnorm w (sub_eq_zero.mp ((mul_eq_zero.mp (hsim w w x x hw hw)).resolve_right hq))

end GlobalTheory
