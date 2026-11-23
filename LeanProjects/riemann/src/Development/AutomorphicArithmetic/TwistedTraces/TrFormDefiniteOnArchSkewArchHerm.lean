import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.TraceMixedSpaceEqMixedTraceLMul

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

open scoped Classical in
private theorem trace_mixedSpace_eq {K : Type} [Field K] [NumberField K]
    (x : NumberField.mixedEmbedding.mixedSpace K) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
      mixedTraceL K x + ∑ v, (x.2 v).re := by
  rw [UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul, mixedTraceL_apply, mixedTraceL_apply]
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, sub_zero, ← Finset.sum_mul]
  ring

open scoped Classical in
private theorem trace_eq_zero_of_star_neg {K : Type} [Field K] [NumberField K]
    (z : NumberField.mixedEmbedding.mixedSpace K) (hz : star z = -z) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) z = 0 := by
  have h1 : mixedTraceL K (star z) = mixedTraceL K z := mixedTraceL_star z
  rw [hz, map_neg] at h1
  have h2 : ∑ v, (z.2 v).re = 0 := by
    have h3 : ∀ v, (z.2 v).re = 0 := fun v => by
      have h4 : star (z.2 v) = -(z.2 v) := congrFun (congrArg Prod.snd hz) v
      have h5 := congrArg Complex.re h4
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h5
      linarith
    simp [h3]
  rw [trace_mixedSpace_eq, h2]
  linarith

open scoped Classical in
private theorem trace_conjTranspose_mul_pos {K : Type} [Field K] [NumberField K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (NumberField.mixedEmbedding.mixedSpace K)} (hA : A ≠ 0) :
    0 < Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
      (Matrix.trace (A.conjTranspose * A)) := by
  rw [trace_mixedSpace_eq]
  have h1 := mixedTraceL_trace_conjTranspose_mul_self_pos hA
  have h2 : 0 ≤ ∑ v, ((Matrix.trace (A.conjTranspose * A)).2 v).re := by
    refine Finset.sum_nonneg fun v _ => ?_
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Prod.snd_sum, Finset.sum_apply, Complex.re_sum, Prod.snd_mul, Pi.mul_apply, Prod.snd_star,
      Pi.star_apply]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  linarith

theorem UpperTheory.trForm_definite_on_archSkew_archHerm :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ X ∈ archSkew K n, X ≠ 0 → trForm K n X X < 0) ∧ (∀ X ∈ archHerm K n, X ≠ 0 → 0 < trForm K n X X) ∧ (∀ X ∈ archSkew K n, ∀ Y ∈ archHerm K n, trForm K n X Y = 0) := by
  intro K _ _ n
  refine ⟨fun X hX h0 => ?_, fun X hX h0 => ?_, fun X hX Y hY => ?_⟩
  · rw [mem_archSkew] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have e : mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n) =
        -((mat (X : ArchMatrix K n)).conjTranspose * mat (X : ArchMatrix K n)) := by
      rw [hX, Matrix.neg_mul, neg_neg]
    have h := trace_conjTranspose_mul_pos hX0
    have h2 : trForm K n X X = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n))) := rfl
    rw [h2, e, Matrix.trace_neg, map_neg]
    linarith
  · rw [mem_archHerm] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have h := trace_conjTranspose_mul_pos hX0
    rw [hX] at h
    exact h
  · rw [mem_archSkew] at hX
    rw [mem_archHerm] at hY
    have h2 : trForm K n X Y = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := rfl
    rw [h2]
    refine trace_eq_zero_of_star_neg _ ?_
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hY, Matrix.mul_neg,
      Matrix.trace_neg, Matrix.trace_mul_comm]
