import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

theorem norm_det_le_add_posSemidef (A P : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (hP : P.PosSemidef) : ‖A.det‖ ≤ ‖(A + P).det‖ := by
  have h1 : imH (I • A) = A := by
    have := imH_add_I_smul 0 A hA.1
    simpa [imH] using this
  have h := (norm_det_denom_mono N 1 0 (I • A) P (by simp) (by simpa using Matrix.PosDef.one)
    (by rwa [h1]) hP).2
  simpa [← smul_add, det_smul] using h

theorem star_dotProduct_self_eq_sum (x : Fin N → ℂ) :
    star x ⬝ᵥ x = ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul']

theorem posSemidef_sub_mul_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) (B : ℝ)
    (hX : ∀ a b, ‖X a b‖ ≤ B) :
    ((((N : ℝ) ^ 2 * B ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (isHermitian_mul_conjTranspose_self X)
    simp [IsHermitian]
  · have h1 : star x ⬝ᵥ (X * Xᴴ) *ᵥ x = star (Xᴴ *ᵥ x) ⬝ᵥ (Xᴴ *ᵥ x) := by
      rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec]
    rw [sub_mulVec, dotProduct_sub, h1, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dotProduct_self_eq_sum, star_dotProduct_self_eq_sum, smul_eq_mul, ← ofReal_mul,
      ← ofReal_sub, Complex.zero_le_real, sub_nonneg]
    have h2 : ∀ a, ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ B ^ 2 * (N * ∑ b, ‖x b‖ ^ 2) := by
      intro a
      have h3 : ‖(Xᴴ *ᵥ x) a‖ ≤ B * ∑ b, ‖x b‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le Finset.univ fun b => Xᴴ a b * x b).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, conjTranspose_apply, norm_star]
        exact mul_le_mul_of_nonneg_right (hX b a) (norm_nonneg _)
      have h4 : (∑ b, ‖x b‖) ^ 2 ≤ N * ∑ b, ‖x b‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b => ‖x b‖)
      calc ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ (B * ∑ b, ‖x b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = B ^ 2 * (∑ b, ‖x b‖) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (sq_nonneg B)
    refine (Finset.sum_le_sum fun a _ => h2 a).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem denom_mul_conjTranspose (C D X : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hX : X.IsHermitian) (δ : ℝ) :
    (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ =
      (C * X + D) * (C * X + D)ᴴ + ((δ : ℂ) ^ 2) • (C * Cᴴ) := by
  have h1 : D * Cᴴ = C * Dᴴ := by simpa using h.eq
  have h2 : star (I * δ : ℂ) = -(I * δ) := by simp
  have h3 : (δ : ℂ) ^ 2 = -((I * δ) * (I * δ)) := by
    have : I * δ * (I * δ) = (I * I) * (δ : ℂ) ^ 2 := by ring
    rw [this, I_mul_I]; ring
  rw [h3]
  generalize (I * δ : ℂ) = t at h2 ⊢
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_smul, conjTranspose_one, hX.eq, h2,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h1]
  module

theorem norm_det_mul_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) :
    (A * Aᴴ).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, star_def, Complex.mul_conj']
  simp

theorem norm_det_denom_compare :
    ∀ (N : ℕ) (δ B : ℝ), 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C D Z : Matrix (Fin N) (Fin N) ℂ, (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef → (∀ a b, ‖(Z + Zᴴ) a b‖ ≤ B) → c * ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ≤ ‖(C * Z + D).det‖ ∧ ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 = (C * Cᴴ + D * Dᴴ).det.re := by
  intro N δ B hδ
  set K : ℝ := (N : ℝ) ^ 2 * (B / 2) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := δ ^ 2 / (2 * δ ^ 2 + 1 + 2 * K) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : 0 ≤ 1 - 2 * c := by
    rw [hc, sub_nonneg, ← mul_div_assoc, div_le_one (by positivity)]
    linarith
  have hc2 : 0 ≤ δ ^ 2 - c - 2 * c * K := by
    have : c * (2 * δ ^ 2 + 1 + 2 * K) = δ ^ 2 := by rw [hc]; field_simp
    nlinarith [mul_pos hc0 (pow_pos hδ 2)]
  refine ⟨Real.sqrt (c ^ N), by positivity, fun C D Z h hp hZ hB => ?_⟩
  have hG : (C * Cᴴ + D * Dᴴ).det =
      ((‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 : ℝ) : ℂ) := by
    have := denom_mul_conjTranspose C D 0 h isHermitian_zero 1
    rw [← norm_det_mul_conjTranspose]
    simp only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at this
    rw [this, add_comm]
  refine ⟨?_, by rw [hG, ofReal_re]⟩
  set X : Matrix (Fin N) (Fin N) ℂ := (2⁻¹ : ℂ) • (Z + Zᴴ) with hXdef
  have hX : X.IsHermitian := by
    simp [hXdef, IsHermitian, add_comm]
  have hXB : ∀ a b, ‖X a b‖ ≤ B / 2 := by
    intro a b
    have := hB a b
    rw [hXdef, Matrix.smul_apply, norm_smul]
    simp only [norm_inv, Complex.norm_ofNat]
    linarith
  have hone : ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hδ)
  have him : imH (X + (I * δ) • 1) = (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    rw [mul_smul, imH_add_I_smul _ _ hone.1, imH, hX.eq]
    simp
  have hZe : X + (I * δ) • 1 + I • (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = Z := by
    have h2 : I * (2 * I)⁻¹ = 2⁻¹ := by field_simp
    rw [smul_sub, imH, smul_smul, smul_smul, h2, hXdef]
    module
  have hm := (norm_det_denom_mono N C D (X + (I * δ) • 1) _ h hp (by rwa [him]) hZ).2
  rw [hZe] at hm
  refine le_trans ?_ hm
  have hP : ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)).PosSemidef := by
    refine (((posSemidef_self_mul_conjTranspose _).smul ?_).add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)).add
      (((posSemidef_sub_mul_conjTranspose X _ hXB).mul_mul_conjTranspose_same C).smul ?_) |>.add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)
    · exact Complex.zero_le_real.2 hc1
    · exact Complex.zero_le_real.2 hc2
    · exact Complex.zero_le_real.2 (by positivity)
    · exact Complex.zero_le_real.2 hc0.le
  have hd := norm_det_le_add_posSemidef _ _ (hp.smul (Complex.zero_lt_real.2 hc0)) hP
  have he : (c : ℂ) • (C * Cᴴ + D * Dᴴ) + ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)) =
      (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ := by
    rw [denom_mul_conjTranspose C D X h hX]
    push_cast
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    module
  rw [he, norm_det_mul_conjTranspose, det_smul, hG, ← ofReal_pow, ← ofReal_mul, norm_real,
    norm_real, Fintype.card_fin, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hd
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt (by positivity)]

end GlobalTheory.SW
