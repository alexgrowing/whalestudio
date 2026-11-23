import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ULieDefs

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ULie
open scoped TensorProduct

private theorem coeff_mem_subalgebra_of_eval_mem {R : Type} [CommRing R] [Algebra ℂ R] (S : Subalgebra ℂ R)
    (F : Polynomial R) (h : ∀ u : ℂ, F.eval (algebraMap ℂ R u) ∈ S) (j : ℕ) : F.coeff j ∈ S := by
  classical
  by_cases hj : F.natDegree + 1 ≤ j
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact S.zero_mem
  push_neg at hj
  let v : Fin (F.natDegree + 1) → ℂ := fun i => ((i : ℕ) : ℂ)
  have hv : Function.Injective v := fun a b hab => Fin.ext (by simpa [v] using hab)
  let V := Matrix.vandermonde v
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  let c : Fin (F.natDegree + 1) → R := fun k => F.coeff k
  have hval : ∀ i, (V.map (algebraMap ℂ R) *ᵥ c) i = F.eval (algebraMap ℂ R (v i)) := by
    intro i
    rw [Polynomial.eval_eq_sum_range' (n := F.natDegree + 1) (by omega), ← Fin.sum_univ_eq_sum_range]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.vandermonde_apply, map_pow, c, V]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hv2 : ∀ i, (V.map (algebraMap ℂ R) *ᵥ c) i ∈ S := fun i => (hval i) ▸ h _
  have hinv : (V⁻¹).map (algebraMap ℂ R) * V.map (algebraMap ℂ R) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul V hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc : c = (V⁻¹).map (algebraMap ℂ R) *ᵥ (V.map (algebraMap ℂ R) *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hcj : F.coeff j = c ⟨j, hj⟩ := rfl
  rw [hcj, hc]
  generalize V.map (algebraMap ℂ R) *ᵥ c = w at hv2
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun i _ => S.mul_mem (S.algebraMap_mem _) (hv2 i)

theorem UpperTheory.isIntegral_eval_of_monic_mul_isIntegral :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (P Q : Polynomial R), P.Monic → Q.Monic → (∀ u : ℂ, IsIntegral ℂ ((P * Q).eval (algebraMap ℂ R u))) → ∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ R u)) := by
  intro R _ _ P Q hP hQ h u
  classical
  have hcoeff : ∀ j, (P * Q).coeff j ∈ integralClosure ℂ R := coeff_mem_subalgebra_of_eval_mem _ (P * Q) h
  have hlift : P * Q ∈ Polynomial.lifts (algebraMap (integralClosure ℂ R) R) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hcoeff n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hP.mul hQ)
  have hPc : ∀ i, P.coeff i ∈ integralClosure ℂ R := by
    intro i
    have hi := Polynomial.isIntegral_coeff_of_dvd q P hqm hP (by rw [hq]; exact dvd_mul_right P Q) i
    exact isIntegral_trans _ hi
  have hmem : P.eval (algebraMap ℂ R u) ∈ integralClosure ℂ R := by
    rw [Polynomial.eval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hPc i)
      (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ u) _)
  exact hmem
