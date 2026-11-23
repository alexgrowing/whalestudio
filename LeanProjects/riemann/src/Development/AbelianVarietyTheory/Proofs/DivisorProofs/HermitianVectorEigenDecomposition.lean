import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Formalism.BasicNotions.TH Matrix

namespace GlobalTheory

theorem hyperbolic_pair_of_cartan_isotropic : ∀ {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ), Mᴴ = M → IsCartan M θ → x ≠ 0 →
    x ⬝ᵥ M *ᵥ star x = 0 →
    ∃ (e f : Fin n → ℂ) (k : ℂ), k ≠ 0 ∧ x = k • (e + f) ∧ θ *ᵥ x = k • (e - f) ∧ θ *ᵥ e = e ∧ θ *ᵥ f = -f ∧
      e ⬝ᵥ M *ᵥ star e = 1 ∧ f ⬝ᵥ M *ᵥ star f = -1 ∧ e ⬝ᵥ M *ᵥ star f = 0 ∧ f ⬝ᵥ M *ᵥ star e = 0 ∧
      ∀ u : Fin n → ℂ, u ⬝ᵥ M *ᵥ star x = 0 → u ⬝ᵥ M *ᵥ star (θ *ᵥ x) = 0 →
        u ⬝ᵥ M *ᵥ star e = 0 ∧ u ⬝ᵥ M *ᵥ star f = 0 ∧ e ⬝ᵥ M *ᵥ star u = 0 ∧ f ⬝ᵥ M *ᵥ star u = 0 := by
  intro n M θ x hM hC hx hxx
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  have hstar : ∀ v : Fin n → ℂ, star (θ *ᵥ v) = θ.map star *ᵥ star v := by
    intro v; ext i; simp [mulVec, dotProduct, star_sum]
  have hisoV : ∀ u v : Fin n → ℂ, (θ *ᵥ u) ⬝ᵥ M *ᵥ star (θ *ᵥ v) = u ⬝ᵥ M *ᵥ star v := by
    intro u v
    rw [hstar, mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, hiso,
      ← dotProduct_mulVec]
  have hherm : ∀ u v : Fin n → ℂ, v ⬝ᵥ M *ᵥ star u = star (u ⬝ᵥ M *ᵥ star v) := by
    intro u v
    rw [← star_dotProduct_star, Matrix.star_mulVec, star_star, hM, ← dotProduct_mulVec]
  have hθθv : ∀ v : Fin n → ℂ, θ *ᵥ (θ *ᵥ v) = v := by
    intro v; rw [mulVec_mulVec, hθθ, one_mulVec]

  set y : Fin n → ℂ := θ *ᵥ x with hy
  have hyy : y ⬝ᵥ M *ᵥ star y = 0 := by rw [hy, hisoV]; exact hxx
  have hxy : x ⬝ᵥ M *ᵥ star y = y ⬝ᵥ M *ᵥ star x := by
    rw [← hisoV x y, hy, hθθv]
  set N : ℝ := (y ⬝ᵥ M *ᵥ star x).re with hN
  have hNpos : 0 < N := hpos x hx
  have hyx : y ⬝ᵥ M *ᵥ star x = (N : ℂ) := by
    have h1 : star (y ⬝ᵥ M *ᵥ star x) = y ⬝ᵥ M *ᵥ star x := by rw [← hherm, hxy]
    have h2 := Complex.conj_eq_iff_re.mp h1
    rw [hN]; exact h2.symm
  have hxy' : x ⬝ᵥ M *ᵥ star y = (N : ℂ) := by rw [hxy, hyx]

  set s : ℝ := Real.sqrt (2 * N) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s * s = 2 * N := Real.mul_self_sqrt (by linarith)
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  set t : ℂ := 1 / (s : ℂ) with ht
  have htstar : star t = t := by rw [ht]; simp [Complex.conj_ofReal]
  have htt : t * t * (2 * (N : ℂ)) = 1 := by
    have : ((s : ℂ) * s) = 2 * (N : ℂ) := by exact_mod_cast hs2
    rw [ht, ← this]; field_simp
  refine ⟨t • (x + y), t • (x - y), (s : ℂ) / 2, div_ne_zero hsc two_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, ht]; field_simp; ring
  · ext i; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, ht]; field_simp; ring
  · rw [mulVec_smul, mulVec_add, hθθv, add_comm]
  · rw [mulVec_smul, mulVec_sub, hθθv, ← smul_neg, neg_sub]
  · simp only [star_smul, htstar, star_add, star_sub, mulVec_smul, mulVec_add, mulVec_sub, dotProduct_smul, smul_dotProduct,
      dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct, smul_eq_mul, hxx, hyy, hxy', hyx]
    linear_combination htt
  · simp only [star_smul, htstar, star_add, star_sub, mulVec_smul, mulVec_add, mulVec_sub, dotProduct_smul, smul_dotProduct,
      dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct, smul_eq_mul, hxx, hyy, hxy', hyx]
    linear_combination -htt
  · simp only [star_smul, htstar, star_add, star_sub, mulVec_smul, mulVec_add, mulVec_sub, dotProduct_smul, smul_dotProduct,
      dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct, smul_eq_mul, hxx, hyy, hxy', hyx]
    ring
  · simp only [star_smul, htstar, star_add, star_sub, mulVec_smul, mulVec_add, mulVec_sub, dotProduct_smul, smul_dotProduct,
      dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct, smul_eq_mul, hxx, hyy, hxy', hyx]
    ring
  · intro u hu1 hu2
    have hue : u ⬝ᵥ M *ᵥ star (t • (x + y)) = 0 := by
      simp only [star_smul, htstar, star_add, mulVec_smul, mulVec_add, dotProduct_smul, dotProduct_add, smul_eq_mul, hu1, hu2]
      ring
    have huf : u ⬝ᵥ M *ᵥ star (t • (x - y)) = 0 := by
      simp only [star_smul, htstar, star_sub, mulVec_smul, mulVec_sub, dotProduct_smul, dotProduct_sub, smul_eq_mul, hu1, hu2]
      ring
    refine ⟨hue, huf, ?_, ?_⟩
    · rw [hherm, hue, star_zero]
    · rw [hherm, huf, star_zero]

end GlobalTheory
