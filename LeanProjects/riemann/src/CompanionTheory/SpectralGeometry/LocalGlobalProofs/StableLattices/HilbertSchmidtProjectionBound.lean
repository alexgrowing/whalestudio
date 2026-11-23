import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose

open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

noncomputable section

namespace GlobalTheory.CompanionTheory.UGeo.Est

variable {n : ℕ}

theorem nsq_nonneg (y : Fin n → ℂ) : 0 ≤ nsq y := Finset.sum_nonneg fun _ _ => by positivity

theorem nsq_add_le (u v : Fin n → ℂ) : nsq (u + v) ≤ 2 * nsq u + 2 * nsq v := by
  simp only [nsq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (u i) (v i)
  have h1 : ‖(u + v) i‖ ^ 2 ≤ (‖u i‖ + ‖v i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]

theorem nsq_mulVec_le (M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    nsq (M *ᵥ y) ≤ Formalism.REAL.hs M * nsq y := by
  have e1 : nsq (M *ᵥ y) = ∑ i, ‖(M *ᵥ y) i‖ ^ 2 := rfl
  have e2 : Formalism.REAL.hs M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := rfl
  rw [e1, e2, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(M *ᵥ y) i‖ ≤ ∑ j, ‖M i j‖ * ‖y j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M i j‖) (fun j => ‖y j‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem nsq_eq_re (y : Fin n → ℂ) : nsq y = (star y ⬝ᵥ y).re := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  simp [← Complex.ofReal_pow]

theorem nsq_unitary {U : Matrix (Fin n) (Fin n) ℂ} (h : Uᴴ * U = 1) (y : Fin n → ℂ) :
    nsq (U *ᵥ y) = nsq y := by
  rw [nsq_eq_re, nsq_eq_re, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

theorem nsq_proj {P : Matrix (Fin n) (Fin n) ℂ} (h1 : Pᴴ = P) (h2 : P * P = P) (y : Fin n → ℂ) :
    nsq (P *ᵥ y) = (star y ⬝ᵥ (P *ᵥ y)).re := by
  rw [nsq_eq_re, Matrix.star_mulVec, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2]

theorem nsq_three {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGrad ε A) (y : Fin n → ℂ) :
    nsq y = nsq (Pm A *ᵥ y) + nsq (Pz A *ᵥ y) + nsq (Pp A *ᵥ y) := by
  rw [nsq_proj (Pm_conj hA) (Pm_idem hA), nsq_proj (Pz_conj hA) (Pz_idem hA),
    nsq_proj (Pp_conj hA) (Pp_idem hA), ← Complex.add_re, ← Complex.add_re, ← dotProduct_add,
    ← dotProduct_add, ← Matrix.add_mulVec, ← Matrix.add_mulVec, sum_proj, Matrix.one_mulVec, nsq_eq_re]

theorem mulVec_col (M P : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (M *ᵥ fun i => P i j) = fun i => (M * P) i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem hs_eq_cols (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs M = ∑ j, nsq (fun i => M i j) := by
  simp only [Formalism.REAL.hs, nsq]
  exact Finset.sum_comm

theorem hs_mul_le_of_cols {X P : Matrix (Fin n) (Fin n) ℂ} {c : ℝ}
    (h : ∀ j, nsq (X *ᵥ fun i => P i j) ≤ c * nsq (fun i => P i j)) :
    Formalism.REAL.hs (X * P) ≤ c * Formalism.REAL.hs P := by
  rw [hs_eq_cols, hs_eq_cols P, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mulVec_col]
  exact h j

theorem hs_sub_comm (M N : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (M - N) = Formalism.REAL.hs (N - M) := by
  simp only [Formalism.REAL.hs, Matrix.sub_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sub_rev]

theorem est : ∀ (n : ℕ) (ε : Fin n → Bool) (A₀ A' : Matrix (Fin n) (Fin n) ℂ) (α β : ℝ) (x : PSub ε A₀) (k : S7.KG ε), IsGrad ε A₀ → IsGrad ε A' → Formalism.REAL.hs (Pm A₀ - Pm A') ≤ 1 / 4 → Formalism.REAL.hs (Pp A₀ - Pp A') ≤ 1 / 4 → 1 ≤ β → β ≤ α → (∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM ((x : S7.UJ ε) * (k : S7.UJ ε))⁻¹ *ᵥ y)) → Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pm A₀) ≤ 4 * n / α ∧ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pz A₀) ≤ 4 * n * β := by
  intro n ε A₀ A' α β x k h0 h' hm hp hβ hβα hyp
  have hβ0 : 0 < β := by linarith
  have hα0 : 0 < α := by linarith
  have hβi0 : 0 ≤ β⁻¹ := (inv_pos.2 hβ0).le
  have hβi1 : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  have hXiX : S7.toM ((x : S7.UJ ε)⁻¹) * S7.toM (x : S7.UJ ε) = 1 := by
    show (((x : S7.UJ ε)⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val *
      (((x : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val = 1
    simp
  have hU : (S7.toM ((k : S7.UJ ε)⁻¹))ᴴ * S7.toM ((k : S7.UJ ε)⁻¹) = 1 := by
    have hk : ((k : S7.UJ ε)⁻¹) ∈ S7.KG ε := (S7.KG ε).inv_mem k.2
    exact Unitary.star_mul_self_of_mem hk.1
  have H : ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤
      nsq (S7.toM ((x : S7.UJ ε)⁻¹) *ᵥ y) := by
    intro y
    have h := hyp y
    have e : S7.toM ((x : S7.UJ ε) * (k : S7.UJ ε))⁻¹ =
        S7.toM ((k : S7.UJ ε)⁻¹) * S7.toM ((x : S7.UJ ε)⁻¹) := by
      rw [_root_.mul_inv_rev]; rfl
    rwa [e, ← Matrix.mulVec_mulVec, nsq_unitary hU] at h
  have s1 : ∀ y : Fin n → ℂ, Pm A₀ *ᵥ y = y → α / 4 * nsq y ≤ nsq (S7.toM ((x : S7.UJ ε)⁻¹) *ᵥ y) := by
    intro y hy
    have e : Pm A' *ᵥ y + (Pm A₀ - Pm A') *ᵥ y = y := by
      rw [Matrix.sub_mulVec, hy]; abel
    have h1 := nsq_add_le (Pm A' *ᵥ y) ((Pm A₀ - Pm A') *ᵥ y)
    rw [e] at h1
    have h2 := nsq_mulVec_le (Pm A₀ - Pm A') y
    have h3 := mul_le_mul_of_nonneg_right hm (nsq_nonneg y)
    have h4 : 0 ≤ β⁻¹ * nsq (Pz A' *ᵥ y) := mul_nonneg hβi0 (nsq_nonneg _)
    have h5 := H y
    have hN : nsq y / 4 ≤ nsq (Pm A' *ᵥ y) := by linarith
    have h6 := mul_le_mul_of_nonneg_left hN hα0.le
    linarith
  have s2 : ∀ y : Fin n → ℂ, Pp A₀ *ᵥ y = 0 →
      3 / 4 * β⁻¹ * nsq y ≤ nsq (S7.toM ((x : S7.UJ ε)⁻¹) *ᵥ y) := by
    intro y hy
    have e : Pp A' *ᵥ y = (Pp A' - Pp A₀) *ᵥ y := by
      rw [Matrix.sub_mulVec, hy, sub_zero]
    have h1 := nsq_mulVec_le (Pp A' - Pp A₀) y
    rw [← e, hs_sub_comm] at h1
    have h2 := mul_le_mul_of_nonneg_right hp (nsq_nonneg y)
    have h3 := nsq_three h' y
    have hN : 3 / 4 * nsq y ≤ nsq (Pm A' *ᵥ y) + nsq (Pz A' *ᵥ y) := by linarith
    have h4 := mul_le_mul_of_nonneg_left hN hβi0
    have h5 : β⁻¹ * nsq (Pm A' *ᵥ y) ≤ α * nsq (Pm A' *ᵥ y) :=
      mul_le_mul_of_nonneg_right (by linarith) (nsq_nonneg _)
    have h6 := H y
    nlinarith
  constructor
  · have hc : ∀ j, nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pm A₀ i j) ≤ 4 / α * nsq (fun i => Pm A₀ i j) := by
      intro j
      have hv : (fun i => Pm A₀ i j) ∈ Vm A₀ := mem_Vm.2 ⟨Pi.single j 1, by ext i; simp⟩
      have hy := stable_of_keeps x.2.1 _ hv
      obtain ⟨z, hz⟩ := mem_Vm.1 hy
      have hP : Pm A₀ *ᵥ (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pm A₀ i j) =
          S7.toM (x : S7.UJ ε) *ᵥ fun i => Pm A₀ i j := by
        rw [← hz, Matrix.mulVec_mulVec, Pm_idem h0]
      have h := s1 _ hP
      rw [Matrix.mulVec_mulVec, hXiX, Matrix.one_mulVec] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hα0]
      linarith
    have h1 := hs_mul_le_of_cols hc
    have h2 := hs_proj_le (Pm_conj h0) (Pm_idem h0)
    have h3 : 4 / α * Formalism.REAL.hs (Pm A₀) ≤ 4 / α * n :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ = 4 * n / α := by ring
  · have hc : ∀ j, nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pz A₀ i j) ≤ 4 * β * nsq (fun i => Pz A₀ i j) := by
      intro j
      have hv : (fun i => Pz A₀ i j) ∈ Wm A₀ := by
        rw [mem_Wm, mulVec_col, Pp_Pz h0]
        rfl
      have hy := mem_Wm.1 (stable_of_keeps x.2.2 _ hv)
      have h := s2 _ hy
      rw [Matrix.mulVec_mulVec, hXiX, Matrix.one_mulVec] at h
      have h1 := mul_le_mul_of_nonneg_left h hβ0.le
      have e : β * (3 / 4 * β⁻¹ * nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pz A₀ i j)) =
          3 / 4 * nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pz A₀ i j) := by
        field_simp
      rw [e] at h1
      have h2 : 0 ≤ β * nsq (fun i => Pz A₀ i j) := mul_nonneg hβ0.le (nsq_nonneg _)
      nlinarith
    have h1 := hs_mul_le_of_cols hc
    have h2 := hs_proj_le (Pz_conj h0) (Pz_idem h0)
    have h3 : 4 * β * Formalism.REAL.hs (Pz A₀) ≤ 4 * β * n :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ = 4 * n * β := by ring

end GlobalTheory.CompanionTheory.UGeo.Est
