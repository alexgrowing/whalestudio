import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralEqOfDerivs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedIntegralLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
open MeasureTheory

open GlobalTheory.SchwClm in
theorem UpperTheory.schwartz_integral_dominated :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
        {Ω : Type} [TopologicalSpace Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω)
        (G : Ω → SchwartzMap V ℂ), Continuous G →
        (∀ a n : ℕ, ∃ w : Ω → ℝ, Integrable w μ ∧ ∀ x, SchwartzMap.seminorm ℂ a n (G x) ≤ w x) →
        ∀ S : SchwartzMap V ℂ, (∀ y, S y = ∫ x, G x y ∂μ) →
        ∀ l : SchwartzMap V ℂ →L[ℂ] ℂ, Integrable (fun x => l (G x)) μ ∧ l S = ∫ x, l (G x) ∂μ := by
  intro V _ _ _ Ω _ _ _ _ μ G hG hdom S hS0 l
  classical
  choose w hw hwb using hdom
  have hS : ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n S x = ∫ p, iteratedFDeriv ℝ n (G p) x ∂μ := by
    intro n x
    have e : (⇑S : V → ℂ) = fun y => ∫ p, G p y ∂μ := funext hS0
    rw [e, GlobalTheory.ParamSchwartz.iteratedFDeriv_integral_eq (μ := μ) (fun t => ⇑(G t))
      (fun t => (G t).smooth ⊤)
      (fun n y => ((GlobalTheory.SchwInt.iterEvalCLM n y).continuous.comp hG).aestronglyMeasurable)
      (fun n => w 0 n) (fun n => hw 0 n)
      (fun n t y => (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ _ _).trans (hwb 0 n t))]
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
  have hw0 : ∀ a n p, 0 ≤ w a n p := fun a n p => (apply_nonneg _ _).trans (hwb a n p)
  have hint : Integrable (fun p => T (G p)) μ := by
    haveI : SecondCountableTopologyEither Ω (WeightedTarget V s) := ⟨Or.inl inferInstance⟩
    refine Integrable.mono' (g := fun p => ∑ i ∈ s, w i.1 i.2 p)
      (integrable_finset_sum s fun i _ => hw i.1 i.2)
      (T.continuous.comp hG).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hw0 i.1 i.2 p)).2 fun i => ?_
    refine ((norm_weightedDeriv_le _ _ (G p)).trans (hwb i.1.1 i.1.2 p)).trans ?_
    exact Finset.single_le_sum (f := fun j : ℕ × ℕ => w j.1 j.2 p) (fun j _ => hw0 j.1 j.2 p) i.2
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
  refine ⟨?_, ?_⟩
  · have := L.integrable_comp hint
    simpa only [hLT] using this
  · rw [← hLT S, hTS, ← ContinuousLinearMap.integral_comp_comm L hint]
    simp_rw [hLT]
