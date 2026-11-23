import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CanonicalPsiNeZeroOfPathBasis

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem finiteDimensional_continuousMultilinearMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (N : ℕ) : FiniteDimensional ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin N => E) ℂ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℂ) (A := ℂ))
    (fun _ _ h => ContinuousMultilinearMap.toMultilinearMap_injective h)

private theorem aestronglyMeasurable_of_continuous {Kg : Type} [TopologicalSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (f : Kg → W) (hf : Continuous f) : AEStronglyMeasurable f μ := by
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  haveI : SecondCountableTopology W := secondCountable_of_proper
  exact hf.aestronglyMeasurable

private theorem integrable_of_continuous_isFiniteMeasure {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (f : Kg → W) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (aestronglyMeasurable_of_continuous μ f hf) C (Filter.Eventually.of_forall fun k => hC k trivial)

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] (Ω : Set E) (G : Kg → E → ℂ)
    (hΩ : IsOpen Ω)
    (hc : ∀ N : ℕ, ContinuousOn (fun y : Kg × E => iteratedFDeriv ℂ N (G y.1) y.2) (Set.univ ×ˢ Ω))
    (hd : ∀ k, ContDiffOn ℂ ∞ (G k) Ω) :
    (∀ N : ℕ, ∀ x ∈ Ω, iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) x = ∫ k, iteratedFDeriv ℂ N (G k) x ∂μ) ∧
      ContDiffOn ℂ ∞ (fun x => ∫ k, G k x ∂μ) Ω := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  have hck : ∀ (N : ℕ) (x : E), x ∈ Ω → Continuous (fun k => iteratedFDeriv ℂ N (G k) x) :=
    fun N x hx => (hc N).comp_continuous (continuous_id.prodMk continuous_const) (fun k => ⟨trivial, hx⟩)
  have hdiff : ∀ (N : ℕ) (k : Kg) (x : E), x ∈ Ω →
      HasFDerivAt (iteratedFDeriv ℂ N (G k)) (fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) x := by
    intro N k x hx
    have h1 := (hd k).differentiableOn_iteratedFDerivWithin (m := N) (by exact_mod_cast WithTop.coe_lt_top _)
      hΩ.uniqueDiffOn
    have h2 : DifferentiableAt ℂ (iteratedFDerivWithin ℂ N (G k) Ω) x :=
      (h1 x hx).differentiableAt (hΩ.mem_nhds hx)
    have h3 : iteratedFDeriv ℂ N (G k) =ᶠ[nhds x] iteratedFDerivWithin ℂ N (G k) Ω :=
      Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => (iteratedFDerivWithin_of_isOpen N hΩ hy).symm)
    exact (h2.congr_of_eventuallyEq h3).hasFDerivAt
  have hnorm : ∀ (N : ℕ) (k : Kg) (x : E),
      ‖fderiv ℂ (iteratedFDeriv ℂ N (G k)) x‖ = ‖iteratedFDeriv ℂ (N + 1) (G k) x‖ := by
    intro N k x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map]
  have hsucc : ∀ (N : ℕ) (k : Kg) (x : E), fderiv ℂ (iteratedFDeriv ℂ N (G k)) x =
      continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ (iteratedFDeriv ℂ (N + 1) (G k) x) := by
    intro N k x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  have hstep : ∀ (N : ℕ) (x : E), x ∈ Ω → HasFDerivAt (fun y => ∫ k, iteratedFDeriv ℂ N (G k) y ∂μ)
      (∫ k, fderiv ℂ (iteratedFDeriv ℂ N (G k)) x ∂μ) x := by
    intro N x hx
    haveI := finiteDimensional_continuousMultilinearMap (E := E) N
    haveI := finiteDimensional_continuousMultilinearMap (E := E) (N + 1)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
    have hcb : Metric.closedBall x (ε / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x (ε / 2))).exists_bound_of_continuousOn
      ((hc (N + 1)).mono (Set.prod_mono le_rfl hcb))
    have hmeas' : AEStronglyMeasurable (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) μ := by
      have : (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) = fun k =>
          continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ (iteratedFDeriv ℂ (N + 1) (G k) x) :=
        funext fun k => hsucc N k x
      rw [this]
      exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (aestronglyMeasurable_of_continuous μ _ (hck (N + 1) x hx))
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (x₀ := x)
      (F := fun y k => iteratedFDeriv ℂ N (G k) y)
      (F' := fun y k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) y) (bound := fun _ => C)
      (Metric.ball_mem_nhds x (half_pos hε))
      (Filter.eventually_of_mem (Metric.ball_mem_nhds x (half_pos hε))
        (fun y hy => aestronglyMeasurable_of_continuous μ _ (hck N y (hcb (Metric.ball_subset_closedBall hy)))))
      (integrable_of_continuous_isFiniteMeasure μ _ (hck N x hx)) hmeas'
      (Filter.Eventually.of_forall fun k y hy => by
        rw [hnorm]
        exact hC (k, y) ⟨trivial, Metric.ball_subset_closedBall hy⟩)
      (integrable_const C)
      (Filter.Eventually.of_forall fun k y hy => hdiff N k y (hcb (Metric.ball_subset_closedBall hy)))
  have key : ∀ N : ℕ, ∀ x ∈ Ω,
      iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) x = ∫ k, iteratedFDeriv ℂ N (G k) x ∂μ := by
    intro N
    induction N with
    | zero =>
      intro x hx
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ N ih =>
      intro x hx
      have hev : iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) =ᶠ[nhds x]
          fun y => ∫ k, iteratedFDeriv ℂ N (G k) y ∂μ :=
        Filter.eventually_of_mem (hΩ.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hstep N x hx).fderiv]
      have hcomm := (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (μ := μ) (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x)
      refine hcomm.symm.trans ?_
      congr 1
  have hdΦ : ∀ (N : ℕ) (x : E), x ∈ Ω → DifferentiableAt ℂ (iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ)) x :=
    fun N x hx => (hstep N x hx).differentiableAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hΩ.mem_nhds hx) (key N))
  refine ⟨key, ?_⟩
  apply contDiffOn_of_continuousOn_differentiableOn
  · intro m _
    exact ContinuousOn.congr (f := iteratedFDeriv ℂ m (fun x => ∫ k, G k x ∂μ))
      (fun x hx => (hdΦ m x hx).continuousAt.continuousWithinAt) (iteratedFDerivWithin_of_isOpen m hΩ)
  · intro m _
    exact DifferentiableOn.congr (f := iteratedFDeriv ℂ m (fun x => ∫ k, G k x ∂μ))
      (fun x hx => (hdΦ m x hx).differentiableWithinAt) (iteratedFDerivWithin_of_isOpen m hΩ)

private theorem iteratedFDeriv_comp_clm_mul_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (L : E →L[ℂ] E) (a : ℂ) (N : ℕ)
    (y : E) (hy : L y ∈ U) :
    iteratedFDeriv ℂ N (fun y => F (L y) * a) y =
      a • (iteratedFDeriv ℂ N F (L y)).compContinuousLinearMap (fun _ => L) := by
  have hopen : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hFL : ContDiffOn ℂ ∞ (F ∘ L) (L ⁻¹' U) := hF.comp L.contDiff.contDiffOn (fun _ h => h)
  have hfun : (fun y => F (L y) * a) = ((ContinuousLinearMap.mul ℂ ℂ).flip a) ∘ (F ∘ L) := by
    funext z
    simp [mul_comm]
  rw [← iteratedFDerivWithin_of_isOpen N hopen hy, hfun,
    ((ContinuousLinearMap.mul ℂ ℂ).flip a).iteratedFDerivWithin_comp_left (hFL y hy) hopen.uniqueDiffOn hy
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    L.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hopen.uniqueDiffOn hy
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    iteratedFDerivWithin_of_isOpen N hU hy]
  ext v
  simp [mul_comm]

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] (F : E → ℂ) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (L : Kg → E →L[ℂ] E) (hL : Continuous L) (c : Kg → ℂ) (hc : Continuous c) :
    IsOpen {y | ∀ k, L k y ∈ U} ∧
      ContDiffOn ℂ ∞ (fun y => ∫ k, F (L k y) * c k ∂μ) {y | ∀ k, L k y ∈ U} ∧
      (∀ (N : ℕ) (y : E), (∀ k, L k y ∈ U) →
        iteratedFDeriv ℂ N (fun y => ∫ k, F (L k y) * c k ∂μ) y =
          ∫ k, iteratedFDeriv ℂ N (fun y => F (L k y) * c k) y ∂μ) ∧
      ∀ (N : ℕ) (y : E), (∀ k, L k y ∈ U) →
        Integrable (fun k => iteratedFDeriv ℂ N (fun y => F (L k y) * c k) y) μ := by
  have hW : IsOpen {y | ∀ k, L k y ∈ U} := by
    rw [isOpen_iff_mem_nhds]
    intro y0 hy0
    have hcont : Continuous fun z : E × Kg => L z.2 z.1 := (hL.comp continuous_snd).clm_apply continuous_fst
    have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := y0) (P := fun y k => L k y ∈ U)
      (fun k _ => hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (hy0 k)))
    filter_upwards [h] with y hy
    exact fun k => hy k trivial
  have hG : ∀ N : ℕ, ContinuousOn (fun p : Kg × E => iteratedFDeriv ℂ N (fun y => F (L p.1 y) * c p.1) p.2)
      (Set.univ ×ˢ {y | ∀ k, L k y ∈ U}) := by
    intro N
    have hDF : ContinuousOn (iteratedFDeriv ℂ N F) U :=
      (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast (WithTop.coe_lt_top _).le)
        hU.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen N hU hx).symm)
    have h1 : ContinuousOn (fun p : Kg × E => iteratedFDeriv ℂ N F (L p.1 p.2)) (Set.univ ×ˢ {y | ∀ k, L k y ∈ U}) :=
      hDF.comp ((hL.comp continuous_fst).clm_apply continuous_snd).continuousOn (fun p hp => hp.2 p.1)
    have h2 : Continuous (fun p : Kg × E => ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => E) (fun _ => E) ℂ (fun _ => L p.1)) :=
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => E) (fun _ => E) ℂ).cont.comp (continuous_pi fun _ => hL.comp continuous_fst)
    refine ContinuousOn.congr (((hc.comp continuous_fst).continuousOn).smul (h2.continuousOn.clm_apply h1)) ?_
    intro p hp
    dsimp only
    rw [iteratedFDeriv_comp_clm_mul_const F U hU hF (L p.1) (c p.1) N p.2 (hp.2 p.1)]
    simp
  have hdG : ∀ k, ContDiffOn ℂ ∞ (fun y => F (L k y) * c k) {y | ∀ k, L k y ∈ U} :=
    fun k => (hF.comp (L k).contDiff.contDiffOn (fun y (hy : ∀ k, L k y ∈ U) => hy k)).mul contDiffOn_const
  obtain ⟨key, hcd⟩ := matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero μ {y | ∀ k, L k y ∈ U} (fun k y => F (L k y) * c k) hW hG hdG
  refine ⟨hW, hcd, fun N y hy => key N y hy, fun N y hy => ?_⟩
  haveI := finiteDimensional_continuousMultilinearMap (E := E) N
  exact integrable_of_continuous_isFiniteMeasure μ _ ((hG N).comp_continuous (continuous_id.prodMk continuous_const) (fun k => ⟨trivial, hy⟩))

private theorem exists_continuous_clm_of_bilinear {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (m : E →ₗ[ℂ] E →ₗ[ℂ] E) : ∃ Lc : E → E →L[ℂ] E, Continuous Lc ∧ ∀ a y, Lc a y = m a y := by
  refine ⟨fun a => LinearMap.toContinuousLinearMap (m a), ?_, fun a y => rfl⟩
  exact LinearMap.continuous_of_finiteDimensional
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℂ] E) ≃ₗ[ℂ] (E →L[ℂ] E)).toLinearMap ∘ₗ m)

theorem sphU : SphU := by
  intro n F U hU hF Kg _ _ _ _ μ _ _ ι hι c hc ιA ιB _ _ _ _ LA LB hLA hLB g hg
  have hF' : ContDiffOn ℂ ∞ F U := hF.of_le le_top
  obtain ⟨Lc, hLc, hLapp⟩ := exists_continuous_clm_of_bilinear (E := M2 n) (LinearMap.mul ℂ (M2 n))
  simp only [LinearMap.mul_apply'] at hLapp
  obtain ⟨hWo, hΦ, key, hint⟩ := exists_ne_zero_smul_mem_of_mem_span' (E := M2 n) μ F U hU hF' (fun k => Lc (ι k)) (hLc.comp hι) c hc
  simp only [hLapp] at hWo hΦ key hint
  have hgW : ∀ k, ι k * g ∈ U := hg
  have hL := detD_detD_comp (fun y => ∫ k, F (ι k * y) * c k ∂μ) _ hWo hΦ g hgW (LA g) (LB g)
  beta_reduce at hL
  simp only [hLA, hLB, ← mul_add]
  rw [hL, key _ g hgW]
  simp only [ContinuousMultilinearMap.integral_apply (hint _ g hgW)]
  have hR : ∀ k, (detD fun T : Matrix ιA ιA ℂ => detD fun S : Matrix ιB ιB ℂ =>
      F (ι k * (g + (LA g) T + (LB g) S))) * c k =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, ↑↑(Equiv.Perm.sign σ) * ↑↑(Equiv.Perm.sign τ) *
        (iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun y => F (ι k * y) * c k) g)
          (Fin.append (fun i => LA g (single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro k
    have hFk : ContDiffOn ℂ ∞ (fun y => F (ι k * y)) {y : M2 n | ∀ k, ι k * y ∈ U} :=
      (hF'.comp (Lc (ι k)).contDiff.contDiffOn (fun y (hy : ∀ k, ι k * y ∈ U) => by rw [hLapp]; exact hy k)).congr
        (fun y _ => by rw [Function.comp_apply, hLapp])
    have h1 := detD_detD_mul_const (fun y => F (ι k * y)) _ hWo hFk g hgW (LA g) (LB g) (c k)
    have h2 := detD_detD_comp (fun y => F (ι k * y) * c k) _ hWo (hFk.mul contDiffOn_const) g hgW (LA g) (LB g)
    beta_reduce at h1 h2
    rw [← h1, h2]
  simp only [hR]
  rw [integral_finset_sum _ (fun σ _ => ?_)]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_finset_sum _ (fun τ _ => ?_)]
    · refine Finset.sum_congr rfl fun τ _ => ?_
      rw [integral_const_mul]
    · exact ((ContinuousMultilinearMap.apply ℂ _ ℂ _).integrable_comp (hint _ g hgW)).const_mul _
  · exact integrable_finset_sum _ fun τ _ =>
      ((ContinuousMultilinearMap.apply ℂ _ ℂ _).integrable_comp (hint _ g hgW)).const_mul _

end PositivityTheory.Rg.Sw.HSt
