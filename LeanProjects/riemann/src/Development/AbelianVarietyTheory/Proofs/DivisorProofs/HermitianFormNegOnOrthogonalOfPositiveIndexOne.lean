import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.SignatureOneForms

theorem form_re_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v : Fin n → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).re = ∑ i, hA.eigenvalues i *
      Complex.normSq ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := RCLike.ofReal ∘ hA.eigenvalues with hd
  set c := star U *ᵥ v with hc
  have hspec : A = U * diagonal d * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hd]
  have h0 := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) hspec
  have h1 : star v ⬝ᵥ A *ᵥ v = star c ⬝ᵥ (diagonal d *ᵥ c) := by
    rw [h0, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [h1]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, hd, Function.comp_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem form_re_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0)
    (i₀ : Fin n) (hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀) (v : Fin n → ℂ) (hv : v ≠ 0)
    (hv0 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i₀ = 0) :
    (star v ⬝ᵥ A *ᵥ v).re < 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set c := star U *ᵥ v with hc
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hcne : c ≠ 0 := by
    intro h0
    apply hv
    have : U *ᵥ c = v := by
      rw [hc, mulVec_mulVec, hU, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec]
    rw [← this, h0, mulVec_zero]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hcne
  have hji : j ≠ i₀ := by
    rintro rfl
    exact hj hv0
  have hjneg : hA.eigenvalues j < 0 :=
    lt_of_le_of_ne (not_lt.mp fun h => hji (hpos j h)) (hne j)
  rw [form_re_eq_sum hA v]
  have key : ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = i₀
      · subst hi
        simp [hv0]
      · have : hA.eigenvalues i ≤ 0 := not_lt.mp fun h => hi (hpos i h)
        nlinarith [Complex.normSq_nonneg (c i)]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      exact mul_neg_of_neg_of_pos hjneg (Complex.normSq_pos.mpr hj)
  simpa using key

end GlobalTheory.SignatureOneForms

namespace GlobalTheory

theorem re_form_neg_of_orth_of_sigPosH_eq_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro n A hA hdet hsig x y hx hxy hy
  unfold sigPosH at hsig
  obtain ⟨⟨i₀, hi₀⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hsig
  have hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀ := fun i h => congrArg Subtype.val (huniq ⟨i, h⟩)
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hyx : star y ⬝ᵥ A *ᵥ x = 0 := by
    have h := congrArg star hxy
    rw [star_zero] at h
    rw [← h, star_dotProduct, star_mulVec, hA.eq, ← dotProduct_mulVec]
  by_contra hQ
  push_neg at hQ
  set a₀ := (star U *ᵥ x) i₀ with ha₀
  set b₀ := (star U *ᵥ y) i₀ with hb₀
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  by_cases ha : a₀ = 0
  · exact absurd (GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos x hx0 ha) (not_lt.mpr hx.le)
  set w := b₀ • x - a₀ • y with hw
  have hw0 : (star U *ᵥ w) i₀ = 0 := by
    simp only [hw, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← ha₀, ← hb₀]
    ring
  have hQw : star w ⬝ᵥ A *ᵥ w = (Complex.normSq b₀ : ℂ) * (star x ⬝ᵥ A *ᵥ x)
      + (Complex.normSq a₀ : ℂ) * (star y ⬝ᵥ A *ᵥ y) := by
    simp only [hw, star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, hxy, hyx, smul_eq_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  by_cases hw' : w = 0
  · have h1 : star x ⬝ᵥ A *ᵥ w = b₀ * (star x ⬝ᵥ A *ᵥ x) := by
      simp [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxy]
    rw [hw', mulVec_zero, dotProduct_zero] at h1
    have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hx; simp at hx
    have hb : b₀ = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hQx
    have : a₀ • y = 0 := by
      have hw2 : b₀ • x - a₀ • y = 0 := hw ▸ hw'
      rw [hb, zero_smul, zero_sub, neg_eq_zero] at hw2
      exact hw2
    exact hy ((smul_eq_zero.mp this).resolve_left ha)
  · have hneg := GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos w hw' hw0
    rw [hQw, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hneg
    nlinarith [Complex.normSq_nonneg a₀, Complex.normSq_nonneg b₀,
      mul_nonneg (Complex.normSq_nonneg b₀) hx.le, mul_nonneg (Complex.normSq_nonneg a₀) hQ]

end GlobalTheory
