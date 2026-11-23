import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.matrix_phi_eq_family : ∀ (R C : Type) [CommRing R] [CommRing C] (i : R →+* C) (φ : C → C) (e e' : R), Associated e e' → ∀ (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') R) (Q Q' : Matrix (Fin d) (Fin d) R), Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R) → ∀ Δ : Matrix (Fin d') (Fin d) C, i e' ^ a • (P.map i * Δ.map φ) = i e ^ a' • (Δ * Q.map i) → ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → R), ∀ j : Fin d' × Fin d, i e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (c k j) := by
  intro R C _ _ i φ e e' he d d' a a' b P Q Q' hQ Δ hΔ
  obtain ⟨u, hu⟩ := he
  have hQm : Q.map i * Q'.map i = (i e') ^ b • (1 : Matrix (Fin d) (Fin d) C) := by
    rw [← Matrix.map_mul, hQ]
    ext x y
    by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
  have key : (i e' ^ a • (P.map i * Δ.map φ)) * Q'.map i
      = (i e ^ a' • (Δ * Q.map i)) * Q'.map i := by rw [hΔ]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Δ, hQm, Matrix.mul_smul, Matrix.mul_one] at key
  refine ⟨a' + b, fun k j => ((u⁻¹ : Rˣ) : R) ^ b * e' ^ a * P j.1 k.1 * Q' k.2 j.2, ?_⟩
  intro j
  have hj := congrFun (congrFun key j.1) j.2
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul] at hj
  rw [Finset.sum_comm] at hj
  have hu' : i e' = i e * i (u : R) := by rw [← hu, map_mul]
  have hinv : i ((u⁻¹ : Rˣ) : R) * i (u : R) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have goalR : ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (((u⁻¹ : Rˣ) : R) ^ b * e' ^ a * P j.1 k.1 * Q' k.2 j.2)
      = i ((u⁻¹ : Rˣ) : R) ^ b * (i e' ^ a * ∑ k1 : Fin d', ∑ k2 : Fin d, i (P j.1 k1) * φ (Δ k1 k2) * i (Q' k2 j.2)) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k2 _ => ?_
    simp only [map_mul, map_pow]; ring
  rw [goalR, hj, hu', mul_pow]
  calc i e ^ (a' + b) * Δ j.1 j.2
      = (i ((u⁻¹ : Rˣ) : R) * i (u : R)) ^ b * (i e ^ (a' + b) * Δ j.1 j.2) := by rw [hinv, one_pow, one_mul]
    _ = _ := by ring
