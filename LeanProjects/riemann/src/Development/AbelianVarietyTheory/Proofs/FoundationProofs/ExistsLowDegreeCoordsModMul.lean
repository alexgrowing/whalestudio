import Mathlib
open Polynomial

namespace GlobalTheory

theorem algebraMap_norm_dvd_polyX {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}
    (b : Module.Basis (Fin n) k[X] A) (g : A) : g ∣ algebraMap k[X] A (Algebra.norm k[X] g) := by
  classical
  set M := Algebra.leftMulMatrix b g with hM
  have hCH : Polynomial.aeval g M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, map_zero, ← hM, Matrix.aeval_self_charpoly]
  have hsplit := Polynomial.X_mul_divX_add M.charpoly
  have h0 : g * Polynomial.aeval g M.charpoly.divX + algebraMap k[X] A (M.charpoly.coeff 0) = 0 := by
    have := congrArg (Polynomial.aeval g) hsplit
    rw [hCH, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
    exact this
  have hdet : Algebra.norm k[X] g = (-1) ^ n * M.charpoly.coeff 0 := by
    rw [Algebra.norm_eq_matrix_det b, ← hM, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
  rw [hdet, map_mul, eq_neg_of_add_eq_zero_right h0]
  exact ⟨-(algebraMap k[X] A ((-1) ^ n) * Polynomial.aeval g M.charpoly.divX), by ring⟩

theorem exists_lowDegree_coords_mod : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  intro k A _ _ _ _ n b g q d hg hq hdeg w
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  have hN : Algebra.norm k[X] g ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  set p₀ := Algebra.norm k[X] g * q with hp₀
  have hp₀0 : p₀ ≠ 0 := mul_ne_zero hN hq
  have hp₀deg : p₀.natDegree ≤ d + 1 := by rw [hp₀, natDegree_mul hN hq]; exact hdeg
  refine ⟨fun i => b.repr w i % p₀, ?_, ?_⟩
  · intro i
    by_cases h0 : b.repr w i % p₀ = 0
    · simp [h0]
    · have hlt : (b.repr w i % p₀).degree < p₀.degree := EuclideanDomain.mod_lt _ hp₀0
      have := Polynomial.natDegree_lt_natDegree h0 hlt
      show (b.repr w i % p₀).natDegree ≤ d
      omega
  · have key : w - ∑ i, (b.repr w i % p₀) • b i
        = algebraMap k[X] A p₀ * ∑ i, (b.repr w i / p₀) • b i := by
      set a := b.repr w with ha
      have hw : w = ∑ i, a i • b i := (b.sum_repr w).symm
      rw [hw, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ← eq_sub_of_add_eq (EuclideanDomain.div_add_mod (a i) p₀), mul_smul,
        Algebra.smul_def]
    rw [key, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := algebraMap_norm_dvd_polyX b g
    refine ⟨c * ∑ i, (b.repr w i / p₀) • b i, ?_⟩
    rw [hp₀, map_mul, hc]
    ring

end GlobalTheory
