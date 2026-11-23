import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HSAbs

theorem coeFn_finsum {X : Type} [MeasurableSpace X] {ν : Measure X} {κ : Type} (s : Finset κ)
    (f : κ → Lp ℂ 2 ν) : (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[ν] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 ν
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

theorem pointwise {X : Type} [MeasurableSpace X] {ν : Measure X}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∀ᵐ x ∂ν, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ≤ C ^ 2 := by
  classical

  let w : (s → ℂ) → H := fun c => ∑ j : s, c j • e j
  have hon : Orthonormal ℂ (fun j : s => e j) := he.comp _ Subtype.val_injective
  have hw2 : ∀ c, ‖w c‖ ^ 2 = ∑ j : s, ‖c j‖ ^ 2 := by
    intro c
    have h := hon.inner_sum c c Finset.univ
    rw [@norm_sq_eq_re_inner ℂ, h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (s → ℂ)
  have hD : ∀ c ∈ D, ∀ᵐ x ∂ν, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    intro c _
    have hlin : T (w c) = ∑ j : s, c j • T (e j) := by
      simp only [w, map_sum, map_smul]
    have hsm : ∀ᵐ x ∂ν, ∀ j : s, (c j • T (e j) : Lp ℂ 2 ν) x = c j * T (e j) x := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (c j) (T (e j))] with x hx
      rw [hx]; rfl
    filter_upwards [hT (w c), coeFn_finsum (ν := ν) Finset.univ (fun j : s => c j • T (e j)), hsm]
      with x hx hsum hj
    rw [hlin, hsum] at hx
    simpa only [hj] using hx
  filter_upwards [(ae_ball_iff hDc).2 hD] with x hx

  have hall : ∀ c : s → ℂ, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    have hcl : IsClosed {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : closure D ⊆ {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      hcl.closure_subset_iff.2 fun c hc => hx c hc
    intro c
    exact hsub (hDd.closure_eq ▸ Set.mem_univ c)

  set S := ∑ j : s, ‖T (e j) x‖ ^ 2 with hS
  have key := hall fun j => (starRingEnd ℂ) (T (e j) x)
  have hL : ‖∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x‖ = S := by
    have : ∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x = ((S : ℝ) : ℂ) := by
      rw [hS]; push_cast
      exact Finset.sum_congr rfl fun j _ => RCLike.conj_mul _
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hR : ‖w (fun j => (starRingEnd ℂ) (T (e j) x))‖ ^ 2 = S := by
    rw [hw2]
    exact Finset.sum_congr rfl fun j _ => by rw [RCLike.norm_conj]
  rw [hL] at key
  have hnn := norm_nonneg (w fun j => (starRingEnd ℂ) (T (e j) x))
  have hfin : S ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - ‖w fun j => (starRingEnd ℂ) (T (e j) x)‖)]
  rw [← Finset.sum_coe_sort s (fun i => ‖T (e i) x‖ ^ 2)]
  exact hfin

theorem sum_le {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∑ i ∈ s, ‖T (e i)‖ ^ 2 ≤ C ^ 2 * ν.real univ := by
  have hn : ∀ f : Lp ℂ 2 ν, ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    intro f
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
    simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rw [integral_ofReal, RCLike.ofReal_re]
  have hint : ∀ f : Lp ℂ 2 ν, Integrable (fun x => ‖f x‖ ^ 2) ν := by
    intro f
    have hm : MemLp f ((2 : ℕ) : ENNReal) ν := by simpa using Lp.memLp f
    exact hm.integrable_norm_pow (by norm_num)
  calc ∑ i ∈ s, ‖T (e i)‖ ^ 2 = ∫ x, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ∂ν := by
        rw [integral_finset_sum s fun i _ => hint (T (e i))]
        exact Finset.sum_congr rfl fun i _ => hn _
    _ ≤ ∫ _x, C ^ 2 ∂ν :=
        integral_mono_ae (integrable_finset_sum s fun i _ => hint (T (e i)))
          (integrable_const _) (pointwise e he T C hT s)
    _ = C ^ 2 * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

end GlobalTheory.HSAbs

open GlobalTheory.HSAbs in

theorem GlobalTheory.isHilbertSchmidt_of_ae_bounded : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  intro X _ ν _ H _ _ _ T C hT
  unfold GlobalTheory.OpTrace.IsHilbertSchmidt
  refine summable_of_sum_le (c := C ^ 2 * ν.real univ) (fun i => sq_nonneg _) fun u => ?_
  exact GlobalTheory.HSAbs.sum_le _ (GlobalTheory.OpTrace.stdBasis H).orthonormal T C hT u
