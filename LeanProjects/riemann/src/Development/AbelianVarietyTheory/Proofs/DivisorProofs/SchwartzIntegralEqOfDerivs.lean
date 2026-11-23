import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivApply
open MeasureTheory

namespace GlobalTheory.SchwClm

abbrev WeightedTarget (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Finset (ℕ × ℕ)) :
    Type :=
  (i : s) → BoundedContinuousFunction V (ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => V) ℂ)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def weightedDeriv (k n : ℕ) (f : SchwartzMap V ℂ) :
    BoundedContinuousFunction V (ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n f x)
    ((continuous_norm.pow k).smul ((f.smooth n).continuous_iteratedFDeriv (le_refl _)))
    (SchwartzMap.seminorm ℂ k n f)
    (fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact f.le_seminorm ℂ k n x)

theorem weightedDeriv_apply (k n : ℕ) (f : SchwartzMap V ℂ) (x : V) :
    weightedDeriv k n f x = (‖x‖ ^ k : ℝ) • GlobalTheory.SchwInt.iterEvalCLM n x f := rfl

theorem norm_weightedDeriv_le (k n : ℕ) (f : SchwartzMap V ℂ) :
    ‖weightedDeriv k n f‖ ≤ SchwartzMap.seminorm ℂ k n f :=
  (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).2 fun x => by
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact f.le_seminorm ℂ k n x

theorem seminorm_le_norm_weightedDeriv (k n : ℕ) (f : SchwartzMap V ℂ) :
    SchwartzMap.seminorm ℂ k n f ≤ ‖weightedDeriv k n f‖ :=
  SchwartzMap.seminorm_le_bound ℂ k n f (norm_nonneg _) fun x => by
    have h := (weightedDeriv k n f).norm_coe_le_norm x
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h

noncomputable def toWeighted (s : Finset (ℕ × ℕ)) : SchwartzMap V ℂ →L[ℂ] WeightedTarget V s :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f i => weightedDeriv i.1.1 i.1.2 f)
    (fun f g => by
      funext i
      ext1 x
      simp only [weightedDeriv_apply, map_add, smul_add, Pi.add_apply,
        BoundedContinuousFunction.coe_add])
    (fun a f => by
      funext i
      ext1 x
      simp only [weightedDeriv_apply, map_smul, RingHom.id_apply, Pi.smul_apply,
        BoundedContinuousFunction.coe_smul]
      exact smul_comm _ _ _)
    ⟨s, 1, zero_le_one, fun f => by
      rw [one_mul]
      refine (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).2 fun i => ?_
      refine (norm_weightedDeriv_le _ _ f).trans ?_
      have := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ V ℂ) (x := f) i.2
      exact this⟩

theorem toWeighted_apply (s : Finset (ℕ × ℕ)) (f : SchwartzMap V ℂ) (i : s) :
    toWeighted s f i = weightedDeriv i.1.1 i.1.2 f := rfl

theorem finset_sup_le_norm_toWeighted (s : Finset (ℕ × ℕ)) (f : SchwartzMap V ℂ) :
    s.sup (schwartzSeminormFamily ℂ V ℂ) f ≤ ‖toWeighted s f‖ := by
  refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  exact (seminorm_le_norm_weightedDeriv i.1 i.2 f).trans
    (norm_le_pi_norm (toWeighted s f) ⟨i, hi⟩)

end GlobalTheory.SchwClm

namespace GlobalTheory.SchwClm

theorem clm_integral_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Type} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    (μ : Measure P) [IsFiniteMeasureOnCompacts μ]
    (G : P → SchwartzMap V ℂ) (hG : Continuous G) (C : Set P) (hCc : IsCompact C)
    (h0 : ∀ p ∉ C, G p = 0)
    (S : SchwartzMap V ℂ) (hS : ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n S x = ∫ p, iteratedFDeriv ℝ n (G p) x ∂μ)
    (l : SchwartzMap V ℂ →L[ℂ] ℂ) : l S = ∫ p, l (G p) ∂μ := by
  classical
  obtain ⟨s, c, -, hc⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp l.toLinearMap) (continuous_norm.comp l.continuous)
  set T : SchwartzMap V ℂ →L[ℂ] WeightedTarget V s := toWeighted s with hTdef
  have hlT : ∀ f, ‖l f‖ ≤ (c : ℝ) * ‖T f‖ := by
    intro f
    have h1 := hc f
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (finset_sup_le_norm_toWeighted s f) c.2)
  set T' : SchwartzMap V ℂ →ₗ[ℂ] WeightedTarget V s := T.toLinearMap
  have hker : LinearMap.ker T' ≤ LinearMap.ker l.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have h := hlT f
    have hf' : T f = 0 := hf
    rw [hf', norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  let l₀ : LinearMap.range T' →ₗ[ℂ] ℂ :=
    (LinearMap.ker T').liftQ l.toLinearMap hker ∘ₗ T'.quotKerEquivRange.symm.toLinearMap
  have hl₀ : ∀ f, l₀ ⟨T f, f, rfl⟩ = l f := by
    intro f
    have e : T'.quotKerEquivRange (Submodule.Quotient.mk f) = ⟨T f, f, rfl⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk T' f)
    simp only [l₀, LinearMap.comp_apply, LinearEquiv.coe_coe, ← e, LinearEquiv.symm_apply_apply,
      Submodule.liftQ_apply, ContinuousLinearMap.coe_coe]
  have hbd : ∀ y : LinearMap.range T', ‖l₀ y‖ ≤ (c : ℝ) * ‖y‖ := by
    intro y
    obtain ⟨f, hf⟩ := y.2
    have hy : y = ⟨T f, f, rfl⟩ := Subtype.ext hf.symm
    rw [hy, hl₀ f]
    exact hlT f
  obtain ⟨L, hL, -⟩ := exists_extension_norm_eq (LinearMap.range T') (l₀.mkContinuous c hbd)
  have hLT : ∀ f, L (T f) = l f := by
    intro f
    rw [hL ⟨T f, f, rfl⟩, LinearMap.mkContinuous_apply, hl₀]
  have hint : Integrable (fun p => T (G p)) μ :=
    GlobalTheory.SchwInt.integrable_of_zero_outside μ (T.continuous.comp hG) hCc
      (fun p hp => by simp [h0 p hp])
  have hTS : T S = ∫ p, T (G p) ∂μ := by
    funext i
    have hi : (∫ p, T (G p) ∂μ) i = ∫ p, T (G p) i ∂μ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun j : s =>
        BoundedContinuousFunction V (ContinuousMultilinearMap ℝ (fun _ : Fin j.1.2 => V) ℂ)) i).integral_comp_comm
          hint).symm
    have hint_i : Integrable (fun p => T (G p) i) μ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun j : s =>
        BoundedContinuousFunction V (ContinuousMultilinearMap ℝ (fun _ : Fin j.1.2 => V) ℂ)) i).integrable_comp hint
    rw [hi]
    ext1 x
    rw [← BoundedContinuousFunction.evalCLM_apply ℂ x (∫ p, T (G p) i ∂μ),
      ← ContinuousLinearMap.integral_comp_comm _ hint_i]
    simp only [BoundedContinuousFunction.evalCLM_apply, hTdef, toWeighted_apply, weightedDeriv_apply,
      GlobalTheory.SchwInt.iterEvalCLM_apply]
    rw [integral_smul, hS]
  rw [← hLT S, hTS, ← ContinuousLinearMap.integral_comp_comm L hint]
  simp_rw [hLT]

end GlobalTheory.SchwClm
