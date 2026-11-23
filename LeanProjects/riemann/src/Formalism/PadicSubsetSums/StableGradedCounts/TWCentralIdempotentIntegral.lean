import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.TW

theorem isIntegral_trace_of_isIntegral {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let L := AlgebraicClosure K
  let φ : Matrix n n K →ₐ[ℤ] Matrix n n L := ((algebraMap K L).mapMatrix).toIntAlgHom
  have hM' : IsIntegral ℤ (φ M) := hM.map φ
  have htr : algebraMap K L M.trace = (φ M).trace := by
    simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := K) (B := L) (algebraMap K L).injective, htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum L (φ M) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM'
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap ℤ L)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (φ M) (p.map (algebraMap ℤ L)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix n n L) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

theorem central_idempotent_integral_twist : CentralIdempotentIntegral := by
  intro K _ _ G _ _ e he hc g
  classical
  set x : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hx
  have hpow : ∀ k : ℕ, x ^ (k + 1) = e * MonoidAlgebra.single (g⁻¹ ^ (k + 1)) 1 := by
    intro k
    induction k with
    | zero => simp [hx]
    | succ k ih =>
      rw [pow_succ, ih, hx, mul_assoc, ← mul_assoc (MonoidAlgebra.single _ _) e, ← hc,
        mul_assoc, ← mul_assoc e e, he, MonoidAlgebra.single_mul_single, ← pow_succ, one_mul]
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hxe : x ^ Fintype.card G = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
    rw [hk, Nat.succ_eq_add_one, hpow, ← Nat.succ_eq_add_one, ← hk, pow_card_eq_one,
      ← MonoidAlgebra.one_def, mul_one]
  have hei : IsIntegral ℤ e := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (by simp), ?_⟩
    simp [pow_two, he]
  have hxi : IsIntegral ℤ x := IsIntegral.of_pow hcard (hxe ▸ hei)
  have hMi : IsIntegral ℤ (Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x) :=
    hxi.map (A := K) (Algebra.leftMulMatrix (MonoidAlgebra.basis G K))
  have htr : (Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x).trace
      = (Fintype.card G : K) * e.coeff g := by
    have : ∀ i : G, Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x i i = e.coeff g := by
      intro i
      rw [Algebra.leftMulMatrix_eq_repr_mul, MonoidAlgebra.basis_apply]
      change (x * MonoidAlgebra.single i 1).coeff i = _
      simp [hx]
    simp [Matrix.trace, this]
  rw [← htr]
  exact isIntegral_trace_of_isIntegral _ hMi

end Formalism.IrreducibleCountingLemmas.TW
