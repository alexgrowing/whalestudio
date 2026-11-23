import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_abs_eq_place {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |reAt v x| = v x := by
  have hw : v.IsReal := IsTotallyReal.isReal v
  rw [← InfinitePlace.norm_embedding_of_isReal hw x]
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply hw x, Complex.ofReal_re, Real.norm_eq_abs]

theorem reAt_sub_place {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x y : F) :
    reAt v (x - y) = reAt v x - reAt v y := by
  unfold reAt
  simp [map_sub]

theorem reAt_zero_place {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) :
    reAt v 0 = 0 := by
  unfold reAt; simp

private theorem infinitePlace_le_of_totally_positive_gap {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ξ η : F)
    (h1 : η = 0 ∨ TP η) (h2 : ξ - η = 0 ∨ TP (ξ - η)) (w : InfinitePlace F) : w η ≤ w ξ := by
  have key : 0 ≤ reAt w η ∧ reAt w η ≤ reAt w ξ := by
    rcases h1 with h1 | h1
    · subst h1
      refine ⟨by simp [reAt_zero_place], ?_⟩
      rcases h2 with h2 | h2
      · rw [sub_zero] at h2
        simp [h2, reAt_zero_place]
      · have := h2 w
        rw [sub_zero] at this
        simpa [reAt_zero_place] using this.le
    · refine ⟨(h1 w).le, ?_⟩
      rcases h2 with h2 | h2
      · rw [sub_eq_zero] at h2
        simp [h2]
      · have := h2 w
        rw [reAt_sub_place] at this
        linarith
  rw [← reAt_abs_eq_place w η, ← reAt_abs_eq_place w ξ, abs_of_nonneg key.1,
    abs_of_nonneg (key.1.trans key.2)]
  exact key.2

theorem finite_tp_box : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (D : ℕ), 0 < D → ∀ ξ : F, {η : F | (η = 0 ∨ TP η) ∧ (ξ - η = 0 ∨ TP (ξ - η)) ∧ IsIntegral ℤ ((D : F) * η)}.Finite := by
  intro F _ _ _ D hD ξ
  have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ ((D : ℝ) * ∑ w : InfinitePlace F, w ξ)
  have hD' : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  refine (Set.Finite.preimage (f := fun η : F => (D : F) * η)
    (fun a _ b _ h => mul_left_cancel₀ hD' h) hfin).subset ?_
  rintro η ⟨h1, h2, h3⟩
  refine ⟨h3, fun φ => ?_⟩
  have hle : (InfinitePlace.mk φ) η ≤ (InfinitePlace.mk φ) ξ := infinitePlace_le_of_totally_positive_gap ξ η h1 h2 _
  have hsum : (InfinitePlace.mk φ) ξ ≤ ∑ w : InfinitePlace F, w ξ :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => w ξ) (fun w _ => apply_nonneg w ξ)
      (Finset.mem_univ _)
  rw [InfinitePlace.apply] at hle
  show ‖φ ((D : F) * η)‖ ≤ (D : ℝ) * ∑ w : InfinitePlace F, w ξ
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hle.trans hsum) (Nat.cast_nonneg _)

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyPositive_summands_with_denominator_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (D : ℕ), 0 < D → ∀ ξ : F, {η : F | (η = 0 ∨ TP η) ∧ (ξ - η = 0 ∨ TP (ξ - η)) ∧ IsIntegral ℤ ((D : F) * η)}.Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.finite_tp_box | exact GlobalTheory.HilbertThetaSeries.finite_tp_box | (intros; apply GlobalTheory.HilbertThetaSeries.finite_tp_box <;> assumption)
