import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem coeff_eq_zero_of_sum_reps_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ))
    (b : SL(2, ℤ) → ℕ → ℂ), 0 < M → IsReps Γ s →
    (∀ (x : SL(2, ℤ)) (n : ℕ), b (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * b x n) →
    (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), b (γ * x) n = b x n) → (∀ (x : SL(2, ℤ)) (n : ℕ), b (-x) n = -b x n) →
    (∀ i, ∑ n ∈ Finset.range M, b (s i) n = 0) → ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → b x n = 0 := by
  intro M Γ r s b hM hs hT hΓ hneg hsum x n hn
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / M)) M :=
    Complex.isPrimitiveRoot_exp M hM.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / M) with hζ
  have hB : ∀ y : SL(2, ℤ), ∑ k ∈ Finset.range M, b y k = 0 := by
    intro y
    obtain ⟨i, γ, hγ, rfl | rfl⟩ := hs.1 y
    · simp only [hΓ γ hγ]; exact hsum i
    · simp only [hneg, hΓ γ hγ, Finset.sum_neg_distrib, hsum i, neg_zero]
  have hTm : ∀ (m : ℕ) (y : SL(2, ℤ)) (k : ℕ), b (y * ModularGroup.T ^ m) k = (ζ ^ k) ^ m * b y k := by
    intro m
    induction m with
    | zero => intro y k; simp
    | succ m ih => intro y k; rw [pow_succ, ← mul_assoc, hT, ih, pow_succ]; ring
  have hinj : Function.Injective (fun j : Fin M => ζ ^ (j : ℕ)) := by
    intro i j h
    exact Fin.ext (hprim.pow_inj i.2 j.2 h)
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (R := ℂ)
    (f := fun j : Fin M => ζ ^ (j : ℕ)) (v := fun j : Fin M => b x j) hinj (by
      intro i
      have h0 := hB (x * ModularGroup.T ^ (i : ℕ))
      rw [← Fin.sum_univ_eq_sum_range] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hTm, mul_comm])
  have := congrFun hv ⟨n, hn⟩
  simpa using this

end GlobalTheory.OddFrame
