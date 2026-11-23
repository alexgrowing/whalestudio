import Mathlib

noncomputable section

namespace PI.Dv.TIW

open Matrix

theorem root_pow_eq_one {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hM : M ^ m = 1)
    (μ : ℂ) (hμ : μ ∈ M.charpoly.roots) : μ ^ m = 1 := by
  have hroot : M.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hMv : M *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, funext_iff, Pi.smul_apply, smul_eq_mul]
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have := hpow m
  rw [hM, Matrix.one_mulVec] at this
  have h2 : (μ ^ m - 1) • v = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv0

theorem trace_finite_order {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hm : 0 < m)
    (hM : M ^ m = 1) : ‖M.trace‖ ≤ Fintype.card d ∧ IsIntegral ℤ M.trace := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  have hroots : ∀ μ ∈ M.charpoly.roots, μ ^ m = 1 := root_pow_eq_one M m hM
  constructor
  · calc ‖M.charpoly.roots.sum‖ ≤ (M.charpoly.roots.map norm).sum := norm_multiset_sum_le _
      _ = (M.charpoly.roots.map (fun _ => (1 : ℝ))).sum := by
          congr 1
          exact Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'
      _ = Multiset.card M.charpoly.roots := by simp
      _ ≤ M.charpoly.natDegree := by exact_mod_cast Polynomial.card_roots' _
      _ = Fintype.card d := by rw [Matrix.charpoly_natDegree_eq_dim]
  · have : ∀ μ ∈ M.charpoly.roots, μ ∈ integralClosure ℤ ℂ := fun μ hμ =>
      IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)
    exact Subalgebra.multiset_sum_mem _ this

theorem trace_end_finite_order {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ Module.finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by
  set b := Module.finBasis K W
  set A := LinearMap.toMatrixAlgEquiv b f with hA
  have htr : LinearMap.trace K W f = A.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b f, hA]; rfl
  have hAm : A ^ m = 1 := by rw [hA, ← map_pow, hf, map_one]
  set B := σ.mapMatrix A with hB
  have hBm : B ^ m = 1 := by rw [hB, ← map_pow, hAm, map_one]
  have hσtr : σ (A.trace) = B.trace := by
    simp [Matrix.trace, hB, map_sum]
  obtain ⟨h1, h2⟩ := trace_finite_order B m hm hBm
  rw [htr, hσtr]
  refine ⟨by simpa using h1, ?_⟩
  rw [← hσtr] at h2
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp h2

end PI.Dv.TIW
