import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Geo
open scoped ContDiff Topology

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem cut_chart (Ψ : ℂ → ℂ) (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun h => Ψ (φ h)) g x = Ψ (chart φ g x) := by
  obtain ⟨y, hy⟩ := hx
  obtain rfl : x = toL y.val := hy.symm
  rw [chart_val, chart_val]

private theorem cut_mem {Ψ : ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (φ : Sm E a) : (fun h => Ψ (φ.1 h)) ∈ Sm E a := fun g =>
  (hΨ.comp_contDiffOn (φ.2 g)).congr fun _ hx => cut_chart Ψ φ.1 g hx

private theorem cut_lie {Ψ : ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (φ : Sm E a) (X : Lie E a) (g : GA E a) :
    (lie E a X ⟨_, cut_mem hΨ φ⟩).1 g = fderiv ℝ Ψ (φ.1 g) ((lie E a X φ).1 g) := by
  have hv : chart φ.1 g (oneL E a) = φ.1 g := by simpa using chart_val φ.1 g 1
  rw [← hv]
  change fderiv ℝ (chart (fun h => Ψ (φ.1 h)) g) (oneL E a) X = fderiv ℝ Ψ _ (fderiv ℝ (chart φ.1 g) (oneL E a) X)
  have e : chart (fun h => Ψ (φ.1 h)) g =ᶠ[𝓝 (oneL E a)] Ψ ∘ chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    exact cut_chart Ψ φ.1 g hx
  rw [e.fderiv_eq, fderiv_comp _ (hΨ.differentiable (by simp) _) (differentiableAt_chart φ.2 g)]
  rfl

private theorem cut_unif (φ : Sm E a) (h : BddDer φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : Lie E a) g, ‖(lie E a X φ).1 g‖ ≤ K * ‖X‖ := by
  obtain ⟨K, hK⟩ := banach_steinhaus (g := fun g : GA E a => fderiv ℝ (chart φ.1 g) (oneL E a)) fun X => by
    obtain ⟨C, hC⟩ := h X []
    refine ⟨C, fun g => ?_⟩
    have := hC g
    rw [List.map_singleton, List.prod_singleton] at this
    exact this
  exact ⟨K, (norm_nonneg _).trans (hK 1), fun X g =>
    ((fderiv ℝ (chart φ.1 g) (oneL E a)).le_opNorm X).trans (mul_le_mul_of_nonneg_right (hK g) (norm_nonneg _))⟩

end SlopeTestRemainingChoices

private theorem cut_lip : ∃ M : NNReal, LipschitzWith M Real.smoothTransition := by
  have hs : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rcases not_and_or.1 hx with h | h
    · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
        (eventually_lt_nhds (not_le.1 h)).mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
      rw [e.deriv_eq, deriv_const]
    · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
        (eventually_gt_nhds (not_le.1 h)).mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
      rw [e.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := (hs.continuous_deriv le_rfl).bounded_above_of_compact_support hc
  exact ⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (by simp)) fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC x).trans (Real.le_coe_toNNReal C)⟩

private noncomputable def cutRe (R : ℝ) (z : ℂ) : ℝ := Real.smoothTransition (R + 1 - z.re)

private noncomputable def cutFn (R : ℝ) (z : ℂ) : ℂ := cutRe R z

private theorem cutRe_smooth (R : ℝ) : ContDiff ℝ ∞ (cutRe R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub Complex.reCLM.contDiff)

private theorem cutFn_smooth (R : ℝ) : ContDiff ℝ ∞ (cutFn R) :=
  Complex.ofRealCLM.contDiff.comp (cutRe_smooth R)

private theorem cutFn_der : ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) z, ‖fderiv ℝ (cutFn R) z‖ ≤ M := by
  obtain ⟨M, hM⟩ := cut_lip
  refine ⟨M, M.2, fun R z => norm_fderiv_le_of_lip' ℝ M.2 (Filter.Eventually.of_forall fun w => ?_)⟩
  have h1 := hM.dist_le_mul (R + 1 - w.re) (R + 1 - z.re)
  rw [Real.dist_eq, Real.dist_eq] at h1
  have h2 : |R + 1 - w.re - (R + 1 - z.re)| ≤ ‖w - z‖ := by
    rw [show R + 1 - w.re - (R + 1 - z.re) = -(w - z).re by rw [Complex.sub_re]; ring, abs_neg]
    exact Complex.abs_re_le_norm _
  rw [cutFn, cutFn, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 M.2)

private theorem cutFn_flat (R : ℝ) (z : ℂ) (h : cutRe R z = 0 ∨ cutRe R z = 1) : fderiv ℝ (cutFn R) z = 0 := by
  have h0 : fderiv ℝ (cutRe R) z = 0 := by
    rcases h with h | h
    · exact IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun w => by
        rw [h]; exact Real.smoothTransition.nonneg _)
    · exact IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun w => by
        rw [h]; exact Real.smoothTransition.le_one _)
  have h1 := (Complex.ofRealCLM.hasFDerivAt.comp z
    ((cutRe_smooth R).differentiable (by simp) z).hasFDerivAt).fderiv
  rw [h0, ContinuousLinearMap.comp_zero] at h1
  exact h1

theorem UpperTheory.V.Lit.Geo.stepCut :
    StepCut := by
  intro E _ _ _ a U f Y C c f₀ H
  obtain ⟨φ, hφ, hb⟩ := H.f_sm
  obtain ⟨K, hK0, hK⟩ := cut_unif φ hb
  obtain ⟨M, hM0, hM⟩ := cutFn_der
  have hc : ∀ t g, f (splitCentre E a t * g) = f g := fun t g => by
    have := H.f_left 1 t g
    rwa [map_one, one_mul] at this
  have hl : ∀ γ g, f (ratGL E a γ * g) = f g := fun γ g => by
    have h1 := H.f_left γ 0 ((splitCentre E a 0)⁻¹ * g)
    have h2 := hc 0 ((splitCentre E a 0)⁻¹ * g)
    rw [mul_assoc, mul_inv_cancel_left] at h1
    rw [mul_inv_cancel_left] at h2
    exact h1.trans h2.symm
  refine ⟨M * K, mul_nonneg hM0 hK0, fun R =>
    ⟨⟨_, cut_mem (cutFn_smooth R) φ⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, fun g => ⟨fun X => ?_, fun hg => ?_, fun hg => ?_⟩⟩⟩
  · intro γ g
    simp only [hφ, hl]
  · intro t g
    simp only [hφ, hc]
  · intro k
    refine Subtype.ext (funext fun g => ?_)
    change cutFn R (φ.1 (g * infGL E a (Unitary.toUnits k))) = cutFn R (φ.1 g)
    rw [hφ, hφ, H.f_cpt]
  · intro k hk
    refine Subtype.ext (funext fun g => ?_)
    change cutFn R (φ.1 (g * finGL E a k)) = cutFn R (φ.1 g)
    rw [hφ, hφ, H.f_lev k hk]
  · intro g
    exact ⟨_, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _, rfl⟩
  · rw [cut_lie (cutFn_smooth R) φ X g, mul_assoc]
    exact ((fderiv ℝ (cutFn R) _).le_opNorm _).trans (mul_le_mul (hM R _) (hK X g) (norm_nonneg _) hM0)
  · have h1 : cutRe R (φ.1 g) = 1 := by
      rw [hφ, cutRe, Complex.ofReal_re, Real.smoothTransition.one_of_one_le (by linarith)]
    refine ⟨?_, fun X => ?_⟩
    · change cutFn R (φ.1 g) = 1
      rw [cutFn, h1, Complex.ofReal_one]
    · rw [cut_lie (cutFn_smooth R) φ X g, cutFn_flat R _ (Or.inr h1)]
      rfl
  · have h1 : cutRe R (φ.1 g) = 0 := by
      rw [hφ, cutRe, Complex.ofReal_re, Real.smoothTransition.zero_of_nonpos (by linarith)]
    refine ⟨?_, fun X => ?_⟩
    · change cutFn R (φ.1 g) = 0
      rw [cutFn, h1, Complex.ofReal_zero]
    · rw [cut_lie (cutFn_smooth R) φ X g, cutFn_flat R _ (Or.inl h1)]
      rfl
