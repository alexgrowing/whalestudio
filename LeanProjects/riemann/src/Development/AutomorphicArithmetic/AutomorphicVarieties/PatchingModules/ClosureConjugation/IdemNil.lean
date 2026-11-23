import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem charpoly_single {F : Type} [CommRing F] {m : ℕ} (i : Fin (m + 1)) :
    (single i i (1 : F)).charpoly = X ^ (m + 1) - X ^ m := by
  rw [← Matrix.diagonal_single, Matrix.charpoly_diagonal, Fin.prod_univ_succAbove _ i]
  simp [Pi.single_apply, Fin.succAbove_ne]
  ring

theorem UpperTheory.V.Pa.idem_nil :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} (D : Det n B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), D.IsCH → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r y = 0 → ∃ M : ℕ, y ^ M ∈ maximalIdeal B • (⊤ : Submodule B E)) ∧ ∀ (e : E) (i : Fin n), IsIdempotentElem e → r e = single i i 1 → D.D B[X] (1 + X ⊗ₜ e) = 1 + X := by
  intro B E F _ _ _ _ _ _ n D r hch hker hchi
  refine ⟨fun y hy => ⟨n, ?_⟩, fun e i he hre => ?_⟩
  · have h0 := ((d_chS D B).2.2 hch).2 y
    have h1 : (X ^ n - D.chi y).map (algebraMap B F) = 0 := by
      rw [Polynomial.map_sub, hchi, hy, Matrix.charpoly_zero]; simp
    have h2 : y ^ n = aeval y (X ^ n - D.chi y) := by simp [h0]
    rw [h2, aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← hker, RingHom.mem_ker, ← coeff_map, h1, coeff_zero]
  · obtain ⟨k, -, hk⟩ := d_idem_rank D e he
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    have hc := hchi e
    rw [hre, charpoly_single] at hc
    have hl : ∀ j, algebraMap B F (D.lam j e) = (-1) ^ j * (X ^ (m + 1) - X ^ m : F[X]).coeff (m + 1 - j) := by
      intro j
      rw [← hc, coeff_map, Det.lam]; simp
    have h3 : (D.D B[X] (1 + X ⊗ₜ e)).map (algebraMap B F) = 1 + X := by
      rw [(d_chi D e).2.2.1, Polynomial.map_sum, Finset.sum_range_succ', Finset.sum_range_succ',
        Finset.sum_eq_zero]
      · simp [hl, coeff_X_pow, add_comm]
      · intro j hj
        rw [Finset.mem_range] at hj
        have a1 : ¬ (m - (j + 1) = m + 1) := by omega
        have a2 : ¬ (m - (j + 1) = m) := by omega
        simp [hl, coeff_X_pow, a1, a2]
    rw [hk] at h3 ⊢
    have h4 := congrArg natDegree h3
    have h5 : natDegree (1 + X : F[X]) = 1 := by rw [add_comm]; exact natDegree_X_add_C 1
    have h6 : Monic (1 + X : F[X]) := by rw [add_comm]; exact monic_X_add_C 1
    rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, h6.natDegree_pow, h5, mul_one] at h4
    rw [h4, pow_one]
