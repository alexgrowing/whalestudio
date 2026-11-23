import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem congr_core {n : ℕ} {B : Type*} [CommRing B] (σ : B →+* B)
    (Nb N'b Mb X X' : Matrix (Fin n) (Fin n) B) (τ τ' s z : B)
    (hz : IsUnit z) (hX : IsUnit X.det) (hX' : IsUnit X'.det)
    (hτ : τ' = s * τ * (z * σ z))
    (h : X * Nb * (X.map σ)ᵀ = τ • Mb)
    (h' : X' * N'b * (X'.map σ)ᵀ = τ' • Mb) :
    ∃ P : Matrix (Fin n) (Fin n) B, IsUnit P.det ∧ N'b = Pᵀ * (s • Nb) * P.map σ := by
  have hW : X'⁻¹ * X' = 1 := Matrix.nonsing_inv_mul _ hX'
  have hW' : (X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hW]
    simp
  have hWd : IsUnit (X'⁻¹).det := by
    have : (X'⁻¹).det * X'.det = 1 := by rw [← Matrix.det_mul, hW, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ this
  have hzX : (z • X).map σ = σ z • X.map σ := by
    ext i j
    simp
  refine ⟨(X'⁻¹ * (z • X))ᵀ, ?_, ?_⟩
  · rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_smul]
    exact hWd.mul ((hz.pow _).mul hX)
  · have hP : ((X'⁻¹ * (z • X))ᵀ).map σ = σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
      have e : (X'⁻¹ * (z • X)).map σ = (X'⁻¹).map σ * (σ z • X.map σ) := by
        rw [Matrix.map_mul, hzX]
      rw [Matrix.transpose_map, e, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul]
    rw [Matrix.transpose_transpose, hP]
    calc N'b = X'⁻¹ * X' * N'b * ((X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
          rw [hW, hW', Matrix.one_mul, Matrix.mul_one]
      _ = X'⁻¹ * (X' * N'b * (X'.map σ)ᵀ) * ((X'⁻¹).map σ)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = X'⁻¹ * ((s * (z * σ z)) • (X * Nb * (X.map σ)ᵀ)) * ((X'⁻¹).map σ)ᵀ := by
          rw [h', h, hτ, smul_smul]
          congr 3
          ring
      _ = X'⁻¹ * (z • X) * (s • Nb) * (σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
          congr 1
          ring

theorem pCongrScale : CongrScale := by
  intro E _ _ _ n M N N' K _ _ θ D hθ hD t t' a b s ht' ht X X' hX hX' h h'
  let F := maximalRealSubfield E
  let B := K ⊗[F] E
  let σ := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  let cB : K →+* B := algebraMap K B
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hmul : ∀ x y : E, inE K (x * y) = inE K x * inE K y := fun x y => by
    simp [inE, Algebra.TensorProduct.tmul_mul_tmul]
  have hrat : ∀ q : ℚ, inE K (q : E) = cB (q : K) := fun q => by
    have e : ((Algebra.TensorProduct.includeRight : E →ₐ[F] B) : E →+* B).comp (Rat.castHom E) =
        cB.comp (Rat.castHom K) := RingHom.ext_rat _ _
    exact congrArg (fun f : ℚ →+* B => f q) e
  have hint : inE K (D : E) = cB (D : K) := by
    have := hrat (D : ℚ)
    simpa using this
  set z : B := cB a + cB b * inE K θ with hzdef
  have hσθ : σ (inE K θ) = -inE K θ := by
    show (1 : K) ⊗ₜ[F] (IsCMField.complexConj E θ) = _
    rw [hθ, TensorProduct.tmul_neg]
  have hσc : ∀ x : K, σ (cB x) = cB x := fun x => σ.commutes x
  have hσz : σ z = cB a - cB b * inE K θ := by
    rw [hzdef, map_add, map_mul, hσc, hσc, hσθ]
    ring
  have hθθ : inE K θ * inE K θ = cB (D : K) := by
    rw [← hmul, ← pow_two, hD, hint]
  have hnorm : z * σ z = cB (a ^ 2 - D * b ^ 2) := by
    rw [hσz, hzdef, map_sub, map_mul, map_pow, map_pow]
    linear_combination (-(cB b) ^ 2) * hθθ
  have hu : (a ^ 2 - D * b ^ 2) ≠ 0 := fun h0 => ht' (by rw [ht, h0, mul_zero])
  have hzu : IsUnit z := by
    have : IsUnit (z * σ z) := by
      rw [hnorm]
      exact (IsUnit.mk0 _ hu).map cB
    exact isUnit_of_mul_isUnit_left this
  have hsm : ∀ (c : K) (A : Matrix (Fin n) (Fin n) B), c • A = cB c • A := fun c A => by
    ext i j
    simp [Algebra.smul_def, cB]
  obtain ⟨P, hP, hE⟩ := congr_core (σ : B →+* B) (N.map (inE K)) (N'.map (inE K)) (M.map (inE K)) X X'
    (cB t) (cB t') (inE K (s : E)) z hzu hX hX' (by
      have hn2 : z * (σ : B →+* B) z = cB (a ^ 2 - D * b ^ 2) := hnorm
      rw [hn2, hrat, ht, map_mul, map_mul])
    (by rw [← hsm]; exact h) (by rw [← hsm]; exact h')
  refine ⟨P, hP, ?_⟩
  have hN : ((s : E) • N).map (fun x => (1 : K) ⊗ₜ[F] x) = inE K (s : E) • N.map (inE K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact hmul _ _
  rw [hN]
  exact hE

end UpperTheory.Gal.G1
