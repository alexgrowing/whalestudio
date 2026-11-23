import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem selfDual_inv_gram_integral (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (w : HeightOneSpectrum (𝓞 E))
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x)))
    (X : Matrix (Fin n) (Fin n) E) (hX : IsUnit X.det) (hG : IsUnit (Xᵀ * J * X.map σ).det)
    (hval : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) (s : 𝓞 E) (hs : s ∉ w.asIdeal)
    (hsr : ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) (i k : Fin n) :
    w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 := by
  set G := Xᵀ * J * X.map σ with hGdef
  set a : Fin n → E := fun j => e * G⁻¹ i j with ha
  have haG : a ᵥ* G = fun j => if j = i then e else 0 := by
    have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
    funext j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [Matrix.vecMul, dotProduct, ha, mul_assoc, ← Finset.mul_sum, h2]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]
  have key : ∀ c : Fin n → E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (X *ᵥ a) (X *ᵥ c) = e * σ (c i) := by
    intro c
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    have h1 : (fun j => σ ((X *ᵥ c) j)) = X.map σ *ᵥ (fun j => σ (c j)) := by
      funext j
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec, haG]
    simp [dotProduct]
  have hXX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  have hXX' : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have hform_smul : ∀ (t : E) (u v : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (t • u) v = t * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J u v := by
    intro t u v
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    rw [smul_dotProduct, smul_eq_mul]
  set y : Fin n → E := (s : E) • (X *ᵥ a) with hy
  have hyL : y ∈ L := by
    refine (hL y).2 fun x hx o => ?_
    obtain ⟨r, hr⟩ := hsr x hx i
    have hx' : X *ᵥ (X⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hXX', Matrix.one_mulVec]
    have h3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x = e * (r : E) := by
      rw [hy, hform_smul, ← hx', key, ← hr]
      ring
    rw [h3]
    have h4 : (o : E) * (e * (r : E)) = ((o * r : 𝓞 E) : E) * e := by
      push_cast; ring
    rw [h4]
    exact he (o * r)
  have h5 := hval y hyL k
  have h6 : (X⁻¹ *ᵥ y) k = (s : E) * (e * G⁻¹ i k) := by
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
    rfl
  rw [h6, map_mul] at h5
  have hsv : w.valuation E (s : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hs
  rw [hsv, one_mul] at h5
  exact h5

end GlobalTheory
