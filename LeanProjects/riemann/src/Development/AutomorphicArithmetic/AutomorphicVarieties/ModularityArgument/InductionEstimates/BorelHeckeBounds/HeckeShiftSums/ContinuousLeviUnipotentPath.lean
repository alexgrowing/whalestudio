import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.LineTerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.CancelN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Master
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BochnerOfLintegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PmLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem ptInv {E X : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (S : E →ₗ[ℂ] (X → ℂ))
    (hS : Function.Injective S) :
    ∃ (n : ℕ) (p : Fin n → X) (T : (Fin n → ℂ) →ₗ[ℂ] E), ∀ e, T (fun i => S e (p i)) = e := by
  classical
  let ev : X → Module.Dual ℂ E := fun x => (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ S
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent ℂ (Set.range ev)
  have hfin : b.Finite := hli.setFinite
  haveI := hfin.fintype
  have hch : ∀ y : b, ∃ x, ev x = y := fun y => hb y.2
  choose q hq using hch
  let e := Fintype.equivFin b
  let R : E →ₗ[ℂ] (Fin (Fintype.card b) → ℂ) :=
    LinearMap.pi fun i => ev (q (e.symm i))
  have hR : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : ∀ y ∈ b, y v = 0 := fun y hy => by
      have := congrFun hv (e ⟨y, hy⟩)
      simpa [R, hq] using this
    have h2 : ∀ y ∈ Submodule.span ℂ b, y v = 0 := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem y hy => exact h1 y hy
      | zero => rfl
      | add y z _ _ hy hz => simp [hy, hz]
      | smul a y _ hy => simp [hy]
    apply hS
    funext x
    rw [map_zero]
    exact h2 (ev x) (hsp ▸ Submodule.subset_span ⟨x, rfl⟩)
  obtain ⟨T, hT⟩ := R.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hR)
  exact ⟨_, fun i => q (e.symm i), T, fun v => LinearMap.congr_fun hT v⟩

private theorem convPt {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]
    (κ : ℝ → V →L[ℂ] W) (hk : Ker κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : L V, ∀ᵐ x : ℝ, ‖conv κ u x‖ ≤ C * ‖u‖ := by
  have hr : MemLp κ 2 (volume : Measure ℝ) := hk.1.memLp_of_hasCompactSupport hk.2
  refine ⟨(eLpNorm κ 2 volume).toReal, ENNReal.toReal_nonneg, fun u => ?_⟩
  filter_upwards [(convSpec κ hk u).1] with x hx
  rw [hx]
  have hmp := measurePreserving_add_left (volume : Measure ℝ) x
  have hg : AEStronglyMeasurable (fun t => u (x + t)) (volume : Measure ℝ) :=
    (Lp.aestronglyMeasurable u).comp_measurePreserving hmp
  have hn : eLpNorm (fun t => u (x + t)) 2 volume = eLpNorm u 2 volume :=
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable u) hmp
  have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1) hr.1 hg
    (fun (A : V →L[ℂ] W) (v : V) => A v) 1 (Eventually.of_forall fun t => by
      rw [one_mul]
      exact (κ t).le_opNNNorm _)
  rw [eLpNorm_one_eq_lintegral_enorm, hn, ENNReal.coe_one, one_mul] at h1
  have h2 := (enorm_integral_le_lintegral_enorm (fun t => κ t (u (x + t)))).trans h1
  rw [← toReal_enorm, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hr.2.ne (Lp.memLp u).2.ne) h2

private theorem inv_map {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (ν : Measure G) [IsProbabilityMeasure ν] (U : Subgroup G) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) : ν.map (fun k => k⁻¹) = ν := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ measurable_inv]
  have h1 : ∫⁻ k, ∫⁻ h, φ (k⁻¹ * h) ∂ν ∂ν = ∫⁻ h, φ h ∂ν := by
    have : ∀ᵐ k ∂ν, ∫⁻ h, φ (k⁻¹ * h) ∂ν = ∫⁻ h, φ h ∂ν :=
      hs.mono fun k hk => (hi _ (U.inv_mem hk)).lintegral_comp hφ
    rw [lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]
  have h2 : ∫⁻ h, ∫⁻ k, φ (k⁻¹ * h) ∂ν ∂ν = ∫⁻ k, φ k⁻¹ ∂ν := by
    have : ∀ᵐ h ∂ν, ∫⁻ k, φ (k⁻¹ * h) ∂ν = ∫⁻ k, φ k⁻¹ ∂ν := hs.mono fun h hh => by
      rw [← (hi _ (U.inv_mem hh)).lintegral_comp (f := fun k => φ k⁻¹) (hφ.comp measurable_inv)]
      simp
    rw [lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]
  rw [← h1, ← h2]
  exact (lintegral_lintegral_swap (f := fun k h => φ (k⁻¹ * h))
    (hφ.comp (measurable_fst.inv.mul measurable_snd)).aemeasurable).symm

private theorem star_hecke {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : CC K n)
    (hf : D.Hecke f) : D.Hecke (CuspidalProjection.ccStar f) := by
  haveI := D.prob
  have hm := inv_map D.ν D.U D.supp D.inv
  have hI : ∀ φ : G1 K n → ℂ, ∫ k, φ k⁻¹ ∂D.ν = ∫ k, φ k ∂D.ν := fun φ => by
    have := integral_map_equiv (μ := D.ν) (MeasurableEquiv.inv (G1 K n)) φ
    rw [show (Measure.map (MeasurableEquiv.inv (G1 K n)) D.ν) = D.ν from hm] at this
    exact this.symm
  intro g
  constructor
  · rw [CuspidalProjection.ccStar_apply, ← (hf g⁻¹).2, ← integral_conj, ← hI]
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    simp [D.star k hk, mul_comm]
  · rw [CuspidalProjection.ccStar_apply, ← (hf g⁻¹).1, ← integral_conj, ← hI]
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    simp [D.star k hk, mul_comm]

private theorem adjBd {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hp : Pair μ₂ τ₁ τ₂) (D : TypeDat K (2 + 2))
    (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d') (a : CC K (2 + 2)) (ha : D.Hecke a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : L2 μ, ∀ᵐ s : ℝ, ‖Jd A.J (Rop μ a ψ) s‖ ≤ C * ‖ψ‖ := by
  obtain ⟨β, hk, hc, -⟩ := convR K μ μ₂ τ₁ τ₂ hp D d d' A A' (CuspidalProjection.ccStar a) (star_hecke D a ha)
  obtain ⟨hs, hadj, -⟩ := convAdj β hk
  obtain ⟨C, hC0, hC⟩ := convPt (sharp β) hs
  refine ⟨C, hC0, fun ψ => ?_⟩
  have e : Jd A.J (Rop μ a ψ) = UpperTheory.V.Z.IntegralApplyAeEq.conv (sharp β) (Jd A.J ψ) := by
    refine ext_inner_left ℂ fun u => ?_
    have h1 : Rop μ (CuspidalProjection.ccStar a) (A.J u) = A.J (UpperTheory.V.Z.IntegralApplyAeEq.conv β u) :=
      hc u _ (convSpec β hk u).1
    rw [← hadj, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    change ⟪A.J u, Rop μ a ψ⟫_ℂ = ⟪A.J (UpperTheory.V.Z.IntegralApplyAeEq.conv β u), ψ⟫_ℂ
    rw [← h1, ← ropAdj, ContinuousLinearMap.adjoint_inner_left]
  have hn : ‖Jd A.J ψ‖ ≤ ‖ψ‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have : ‖Jd A.J‖ ≤ 1 := by
      rw [Jd, LinearIsometryEquiv.norm_map]
      exact A.J.norm_toContinuousLinearMap_le
    exact mul_le_of_le_one_left (norm_nonneg _) this
  filter_upwards [hC (Jd A.J ψ)] with s hs'
  rw [e]
  exact hs'.trans (mul_le_mul_of_nonneg_left hn hC0)

private theorem aeId {d : ℕ} (W : L (Eu d)) (U : ℝ → Eu d) (hU : Continuous U)
    (h : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) →
      ⟪u, W⟫_ℂ = ∫ t, conj (β t) * ⟪v, U t⟫_ℂ) : ∀ᵐ s : ℝ, W s = U s := by
  have hW : LocallyIntegrable (fun x => W x) (volume : Measure ℝ) := (Lp.memLp W).locallyIntegrable (by norm_num)
  have hUl : LocallyIntegrable U (volume : Measure ℝ) := hU.locallyIntegrable
  have hz : ∀ᵐ x : ℝ, W x - U x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hW.sub hUl) fun g hg hc => ?_
    have i1 : Integrable (fun x => g x • W x) (volume : Measure ℝ) :=
      hW.integrable_smul_left_of_hasCompactSupport hg.continuous hc
    have i2 : Integrable (fun x => g x • U x) (volume : Measure ℝ) :=
      hUl.integrable_smul_left_of_hasCompactSupport hg.continuous hc
    simp only [smul_sub]
    rw [integral_sub i1 i2, sub_eq_zero]
    refine ext_inner_left ℂ fun v => ?_
    rw [← integral_inner i1, ← integral_inner i2]
    have hβ : Continuous fun x => (g x : ℂ) := Complex.continuous_ofReal.comp hg.continuous
    have hβc : HasCompactSupport fun x => (g x : ℂ) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    obtain ⟨u, hu⟩ := (denseCc d).2.1 _ v hβ hβc
    have h0 := h _ v u hβ hβc hu
    rw [L2.inner_def] at h0
    have e1 : ∫ x, ⟪v, g x • W x⟫_ℂ = ∫ x, ⟪u x, W x⟫_ℂ := by
      refine integral_congr_ae ?_
      filter_upwards [hu] with x hx
      rw [hx, inner_smul_left, Complex.conj_ofReal, ← Complex.coe_smul, inner_smul_right]
    rw [e1, h0]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.conj_ofReal]
    rw [← Complex.coe_smul, inner_smul_right]
  filter_upwards [hz] with x hx
  exact sub_eq_zero.1 hx

private theorem bdAll {E : Type} [NormedAddCommGroup E] (U : ℝ → E) (hU : Continuous U) (B : ℝ)
    (h : ∀ᵐ s : ℝ, ‖U s‖ ≤ B) (s : ℝ) : ‖U s‖ ≤ B := by
  have hd : Dense {x : ℝ | ‖U x‖ ≤ B} := Measure.dense_of_ae h
  have hc : IsClosed {x : ℝ | ‖U x‖ ≤ B} := isClosed_le hU.norm continuous_const
  have : s ∈ closure {x : ℝ | ‖U x‖ ≤ B} := hd s
  rwa [hc.closure_eq] at this

set_option synthInstance.maxHeartbeats 400000 in
private theorem exK (K : Type) [Field K] [NumberField K] : ∃ κ : Measure (KG K (2 + 2)), κ.IsHaarMeasure := by
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  exact ⟨Measure.haar, inferInstance⟩

private theorem continuous_levi_unipotent_path (K : Type) [Field K] [NumberField K] (h : G1 K (2 + 2)) (r : ℝ) :
    Continuous fun s : ℝ => (lv (1 : G1 K 2) 1 (s - r) * h : G1 K (2 + 2)) := by
  have h1 : Continuous fun s : ℝ => ((1 : G1 K 2), (1 : G1 K 2), s - r) := by fun_prop
  exact (Continuous.comp (g := fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2) (blkLaws (K := K)).2.2.2.1 h1).mul
    continuous_const

private theorem five {M₁ M₂ T Kc U : Type} [MeasurableSpace M₁] [MeasurableSpace M₂] [MeasurableSpace T] [MeasurableSpace Kc]
    [MeasurableSpace U] (a₁ : Measure M₁) (a₂ : Measure M₂) (τ : Measure T) (κ : Measure Kc) (ν : Measure U)
    [SFinite a₁] [SFinite a₂] [SFinite τ] [SFinite κ] [SFinite ν] (G : M₁ × M₂ × T × Kc × U → ℂ)
    (h : Integrable G (a₁.prod (a₂.prod (τ.prod (κ.prod ν))))) :
    ∫ p, G p ∂(a₁.prod (a₂.prod (τ.prod (κ.prod ν)))) =
      ∫ m₁, ∫ m₂, ∫ t, ∫ k, ∫ X, G (m₁, m₂, t, k, X) ∂ν ∂κ ∂τ ∂a₂ ∂a₁ := by
  rw [integral_prod _ h]
  refine integral_congr_ae ?_
  filter_upwards [h.prod_right_ae] with m₁ h1
  rw [integral_prod _ h1]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae] with m₂ h2
  rw [integral_prod _ h2]
  refine integral_congr_ae ?_
  filter_upwards [h2.prod_right_ae] with t h3
  rw [integral_prod _ h3]

private theorem swap {M Z : Type} [MeasurableSpace M] [MeasurableSpace Z] (a : Measure M) (ζ : Measure Z) [IsFiniteMeasure a]
    [SFinite ζ] (u : Z → ℂ) (hu : Integrable u ζ) (b : M → M → Z → ℂ)
    (hb : StronglyMeasurable fun p : (M × M) × Z => b p.1.1 p.1.2 p.2) (C : ℝ) (hC : ∀ x y z, ‖b x y z‖ ≤ C) :
    (∀ x y, Integrable (fun z => u z * b x y z) ζ) ∧
    Integrable (fun m : M × M => ∫ z, u z * b m.1 m.2 z ∂ζ) (a.prod a) ∧
    Integrable (fun z => u z * ∫ x, ∫ y, b x y z ∂a ∂a) ζ ∧
    ∫ m : M × M, ∫ z, u z * b m.1 m.2 z ∂ζ ∂(a.prod a) = ∫ z, u z * ∫ x, ∫ y, b x y z ∂a ∂a ∂ζ := by
  have h0 : Integrable (fun p : (M × M) × Z => u p.2 * b p.1.1 p.1.2 p.2) ((a.prod a).prod ζ) :=
    (hu.comp_snd (a.prod a)).mul_bdd hb.aestronglyMeasurable (Eventually.of_forall fun p => hC _ _ _)
  have h1 : ∀ z, ∫ m : M × M, u z * b m.1 m.2 z ∂(a.prod a) = u z * ∫ x, ∫ y, b x y z ∂a ∂a := by
    intro z
    rw [integral_const_mul, integral_prod]
    exact Integrable.of_bound (hb.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
      (Eventually.of_forall fun p => hC _ _ _)
  refine ⟨fun x y => ?_, h0.integral_prod_left, ?_, ?_⟩
  · exact hu.mul_bdd (hb.comp_measurable (g := fun z => ((x, y), z)) (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun p => hC _ _ _)
  · simpa only [h1] using h0.integral_prod_right
  · rw [integral_integral_swap (f := fun (m : M × M) z => u z * b m.1 m.2 z) h0]
    simp only [h1]

private theorem oneS {ι M Kc : Type} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Kc] (a : Measure M) (κ : Measure Kc)
    [IsFiniteMeasure a] [IsFiniteMeasure κ] (u : ι → ℝ → ℂ) (hu : ∀ i, Integrable (u i)) (b : ι → M → M → Kc → ℂ)
    (hb : ∀ i, StronglyMeasurable fun p : (M × M) × Kc => b i p.1.1 p.1.2 p.2) (C : ι → ℝ) (hC : ∀ i x y k, ‖b i x y k‖ ≤ C i) :
    ∫ x, ∫ y, ∫ t, ∫ k, ∑ i, u i t * b i x y k ∂κ ∂volume ∂a ∂a =
      ∑ i, (∫ t, u i t) * ∫ k, ∫ x, ∫ y, b i x y k ∂a ∂a ∂κ := by
  let Q : ι → M × M → ℂ := fun i m => ∫ k, b i m.1 m.2 k ∂κ
  have hQ : ∀ i, StronglyMeasurable (Q i) := fun i => (hb i).integral_prod_right'
  have hQb : ∀ i m, ‖Q i m‖ ≤ C i * κ.real univ := fun i m =>
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun k => hC i _ _ k)
  have hS : ∀ i x y, Integrable (b i x y) κ := fun i x y =>
    Integrable.of_bound ((hb i).comp_measurable (g := fun z => ((x, y), z))
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable (C i) (Eventually.of_forall fun k => hC i _ _ k)
  have hY : ∀ i x, Integrable (fun y => Q i (x, y)) a := fun i x =>
    Integrable.of_bound ((hQ i).comp_measurable (g := fun y => (x, y)) (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      _ (Eventually.of_forall fun y => hQb i _)
  have hX : ∀ i, Integrable (fun x => ∫ y, Q i (x, y) ∂a) a := fun i =>
    Integrable.of_bound (hQ i).integral_prod_right'.aestronglyMeasurable (C i * κ.real univ * a.real univ)
      (Eventually.of_forall fun x => norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => hQb i _))
  have hM : ∀ i, Integrable (Q i) (a.prod a) := fun i =>
    Integrable.of_bound (hQ i).aestronglyMeasurable _ (Eventually.of_forall fun m => hQb i m)
  have e1 : ∀ x y, ∫ t, ∫ k, ∑ i, u i t * b i x y k ∂κ = ∑ i, (∫ t, u i t) * Q i (x, y) := by
    intro x y
    have : ∀ t, ∫ k, ∑ i, u i t * b i x y k ∂κ = ∑ i, u i t * Q i (x, y) := by
      intro t
      rw [integral_finset_sum _ fun i _ => (hS i x y).const_mul _]
      simp only [integral_const_mul, Q]
    simp only [this]
    rw [integral_finset_sum _ fun i _ => (hu i).mul_const _]
    simp only [integral_mul_const]
  simp only [e1]
  have e2 : ∀ x, ∫ y, ∑ i, (∫ t, u i t) * Q i (x, y) ∂a = ∑ i, (∫ t, u i t) * ∫ y, Q i (x, y) ∂a := by
    intro x
    rw [integral_finset_sum _ fun i _ => (hY i x).const_mul _]
    simp only [integral_const_mul]
  simp only [e2]
  rw [integral_finset_sum _ fun i _ => (hX i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  have h := (swap a κ (fun _ => 1) (integrable_const 1) (b i) (hb i) (C i) (hC i)).2.2.2
  simp only [one_mul] at h
  rw [← h, integral_prod _ (hM i)]
private theorem bf_lv {K : Type} [Field K] [NumberField K] {f : G1 K (2 + 2) → ℂ} (hf : SFun f) (β : ℝ → ℂ) (x y : G1 K 2) (t : ℝ)
    (g : G1 K (2 + 2)) :
    bf β f (lv x y t * g) = β (t + HH g) * Complex.exp (2 * ((t : ℂ) + (HH g : ℂ))) * f (lv x y 0 * g) := by
  have h1 : HP 2 2 (lv x y t * g) = t + HH g := by
    have := (hpSpec (K := K)).1 0 x y t g
    rwa [show nn (0 : UPos (2 + 2) 2 → 𝔸[K]) = 1 from unipOne_zero 2, one_mul] at this
  have h2 : f (lv x y t * g) = f (lv x y 0 * g) := by
    rw [← hf.ray t (lv x y 0 * g), ← mul_assoc, (blkLaws (K := K)).2.1, one_mul, one_mul, add_zero]
  rw [bf, h1, h2]
  congr 3
  push_cast
  ring

private theorem innerX {K : Type} [Field K] [NumberField K] {f : G1 K (2 + 2) → ℂ} (hf : SFun f) (β : ℝ → ℂ) (hβ : Continuous β)
    (hβs : HasCompactSupport β) (Φ : G1 K (2 + 2) → ℂ) {d d' : ℕ} (sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ))
    (sec' : Eu d' →ₗ[ℂ] (G1 K (2 + 2) → ℂ)) (U : ℝ → Eu d) (U' : ℝ → Eu d') (hs : ∀ w, SFun (sec w)) (hs' : ∀ w, SFun (sec' w))
    (hQ : ∀ z, ct 2 Φ z = secF sec U z + secF sec' U' z) (x y : G1 K 2) (t : ℝ) (k : G1 K (2 + 2)) (hk : k ∈ KG K (2 + 2)) :
    (Real.exp (-4 * t) : ℂ) * ∫ X in unipFundamentalDomain K (2 + 2) 2,
      conj (bf β f (nn X * lv x y t * k)) * Φ (nn X * lv x y t * k) ∂unipMeasure K (2 + 2) 2 =
    conj (β t) * (conj (f (lv x y 0 * k)) * (sec (U t) (lv x y 0 * k) + sec' (U' t) (lv x y 0 * k))) := by
  obtain ⟨hP, -, -⟩ := bfFun f β hf hβ hβs
  have hk0 := ((hpSpec (K := K)).2.1 k hk).1
  have hH : HH (lv x y t * k) = t := by
    have := (hpSpec (K := K)).1 0 x y t k
    rwa [show nn (0 : UPos (2 + 2) 2 → 𝔸[K]) = 1 from unipOne_zero 2, one_mul, hk0, add_zero] at this
  have hr : ∀ {h : G1 K (2 + 2) → ℂ}, SFun h → h (lv x y t * k) = h (lv x y 0 * k) := fun hh => by
    rw [← hh.ray t (lv x y 0 * k), ← mul_assoc, (blkLaws (K := K)).2.1, one_mul, one_mul, add_zero]
  have e1 : ∀ X : UPos (2 + 2) 2 → 𝔸[K], bf β f (nn X * (lv x y t * k)) =
      β t * Complex.exp (2 * (t : ℂ)) * f (lv x y 0 * k) := by
    intro X
    rw [hP.unip, bf_lv hf, hk0]
    simp
  simp only [mul_assoc (nn _), e1]
  rw [integral_const_mul]
  have e2 : ∫ X in unipFundamentalDomain K (2 + 2) 2, Φ (nn X * (lv x y t * k)) ∂unipMeasure K (2 + 2) 2 =
      ct 2 Φ (lv x y t * k) := rfl
  have e3 : conj (Complex.exp (2 * (t : ℂ))) = Complex.exp (2 * (t : ℂ)) := by
    have h2 : (2 * (t : ℂ)) = ((2 * t : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.exp_conj, Complex.conj_ofReal]
  have hE : (Real.exp (-4 * t) : ℂ) * Complex.exp (2 * (t : ℂ)) * Complex.exp (2 * (t : ℂ)) = 1 := by
    push_cast
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  rw [e2, hQ, secF, secF, hH, hr (hs _), hr (hs' _), map_mul, map_mul, e3]
  linear_combination (conj (β t) * (conj (f (lv x y 0 * k)) * (sec (U t) (lv x y 0 * k) + sec' (U' t) (lv x y 0 * k)))) * hE

private theorem sec_exp {e : ℕ} {X : Type} (sec : Eu e →ₗ[ℂ] (X → ℂ)) (w : Eu e) (g : X) :
    sec w g = ∑ i, w i * sec (EuclideanSpace.basisFun (Fin e) ℂ i) g := by
  have h := (EuclideanSpace.basisFun (Fin e) ℂ).sum_repr w
  conv_lhs => rw [← h]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, EuclideanSpace.basisFun_repr]

private theorem inner_exp {e : ℕ} (v w : Eu e) :
    ⟪v, w⟫_ℂ = ∑ i, w i * ⟪v, EuclideanSpace.basisFun (Fin e) ℂ i⟫_ℂ := by
  have h := (EuclideanSpace.basisFun (Fin e) ℂ).sum_repr w
  conv_lhs => rw [← h]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, EuclideanSpace.basisFun_repr]

set_option synthInstance.maxHeartbeats 400000 in
private theorem ipSec {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hp : Pair μ₂ τ₁ τ₂) (D : TypeDat K (2 + 2))
    (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d') (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (c : ℝ)
    (hU : Unf μ μ₂ κ c) (Φ : G1 K (2 + 2) → ℂ) (hΦ : Continuous Φ) (hi : ∀ γ ∈ Gam K (2 + 2), ∀ g, Φ (γ * g) = Φ g)
    (w₀ : L2 μ) (hw : Reps μ w₀ Φ) (U : ℝ → Eu d) (U' : ℝ → Eu d') (hUc : Continuous U) (hUc' : Continuous U')
    (hQ : ∀ z, ct 2 Φ z = secF A.sec U z + secF A'.sec U' z) (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)) (hβ : Continuous β)
    (hβs : HasCompactSupport β) (hu : ∀ᵐ x : ℝ, u x = β x • v) :
    ⟪A.J u, w₀⟫_ℂ = ∫ t, conj (β t) * ⟪v, U t⟫_ℂ := by
  haveI := isFiniteMeasure_quotientMeasure μ₂
  haveI : IsFiniteMeasure (fd μ₂) := isFiniteMeasure_restrict.2 (measure_fundamentalDomain_pos_lt_top (Gam K 2) μ₂).2.ne
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : IsFiniteMeasure κ := CompactSpace.isFiniteMeasure
  haveI : SFinite (fd μ₂) := inferInstance
  haveI : SFinite κ := inferInstance
  haveI : SecondCountableTopology (KG K (2 + 2)) := TopologicalSpace.Subtype.secondCountableTopology _
  have hs : ∀ w, SFun (A.sec w) := fun w =>
    secFun μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ ((A.onto (A.sec w)).1 ⟨_, rfl⟩).1 ((A.onto (A.sec w)).1 ⟨_, rfl⟩).2
  have hs' : ∀ w, SFun (A'.sec w) := fun w =>
    secFun μ₂ τ₂ τ₁ D hp.irr₂ hp.irr₁ _ ((A'.onto (A'.sec w)).1 ⟨_, rfl⟩).1 ((A'.onto (A'.sec w)).1 ⟨_, rfl⟩).2
  obtain ⟨hP, hB, hD⟩ := bfFun (A.sec v) β (hs v) hβ hβs
  have hv : Reps μ (A.J u) (th (bf β (A.sec v))) := A.spec β v u hβ hβs hu
  obtain ⟨hI, hE⟩ := (master μ μ₂ κ c hU _ hP.cont hP.rat hB hD _ w₀ hv).2.2 Φ hΦ hi hw
  obtain ⟨hs₁, hs₀⟩ := secIp K μ μ₂ τ₁ τ₂ hp D d d' A A' κ c hU
  let e := EuclideanSpace.basisFun (Fin d) ℂ
  let e' := EuclideanSpace.basisFun (Fin d') ℂ
  let ui : Fin d ⊕ Fin d' → ℝ → ℂ := Sum.elim (fun i t => conj (β t) * U t i) (fun j t => conj (β t) * U' t j)
  let sv : Fin d ⊕ Fin d' → G1 K (2 + 2) → ℂ := Sum.elim (fun i => A.sec (e i)) (fun j => A'.sec (e' j))
  let bi : Fin d ⊕ Fin d' → G1 K 2 → G1 K 2 → KG K (2 + 2) → ℂ := fun i x y k =>
    conj (A.sec v (lv x y 0 * k.1)) * sv i (lv x y 0 * k.1)
  have hsv : ∀ i, SFun (sv i) := by
    rintro (i | j)
    · exact hs _
    · exact hs' _
  have hcj : Continuous fun t => conj (β t) := Complex.continuous_conj.comp hβ
  have hcs : HasCompactSupport fun t => conj (β t) := hβs.comp_left (g := fun z : ℂ => conj z) (by simp)
  have hui : ∀ i, Integrable (ui i) := by
    rintro (i | j)
    · exact (hcj.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
    · exact (hcj.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hlv : Continuous fun p : (G1 K 2 × G1 K 2) × KG K (2 + 2) => (lv p.1.1 p.1.2 0 * p.2.1 : G1 K (2 + 2)) := by
    have h1 : Continuous fun p : (G1 K 2 × G1 K 2) × KG K (2 + 2) => (p.1.1, p.1.2, (0 : ℝ)) := by fun_prop
    exact (Continuous.comp (g := fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2) (blkLaws (K := K)).2.2.2.1 h1).mul
      (continuous_subtype_val.comp continuous_snd)
  have hbi : ∀ i, StronglyMeasurable fun p : (G1 K 2 × G1 K 2) × KG K (2 + 2) => bi i p.1.1 p.1.2 p.2 := fun i =>
    ((Complex.continuous_conj.comp ((hs v).cont.comp hlv)).mul ((hsv i).cont.comp hlv)).stronglyMeasurable
  obtain ⟨C₀, hC₀⟩ := (hs v).bdd
  choose C hC using fun i => (hsv i).bdd
  have hbd : ∀ i x y k, ‖bi i x y k‖ ≤ C₀ * C i := fun i x y k => by
    simp only [bi, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hC₀ _) (hC i _) (norm_nonneg _) ((norm_nonneg _).trans (hC₀ (1 : G1 K (2 + 2))))
  have key := oneS (fd μ₂) κ ui hui bi hbi _ hbd
  have hex : ∀ (x y : G1 K 2) (t : ℝ) (k : KG K (2 + 2)),
      conj (β t) * (conj (A.sec v (lv x y 0 * k.1)) * (A.sec (U t) (lv x y 0 * k.1) + A'.sec (U' t) (lv x y 0 * k.1))) =
        ∑ i, ui i t * bi i x y k := by
    intro x y t k
    rw [Fintype.sum_sum_type, sec_exp A.sec (U t), sec_exp A'.sec (U' t), mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [ui, bi, sv, Sum.elim_inl, Sum.elim_inr]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have nest : ∫ x, ∫ y, ∫ t, ∫ k, ∫ X, conj (bf β (A.sec v) (pt (x, y, t, k, X))) * Φ (pt (x, y, t, k, X))
      ∂((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) ∂κ
      ∂((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))) ∂fd μ₂ ∂fd μ₂ =
      ∫ x, ∫ y, ∫ t, ∫ k, ∑ i, ui i t * bi i x y k ∂κ ∂volume ∂fd μ₂ ∂fd μ₂ := by
    refine integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun y => ?_))
    beta_reduce
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    exact (innerX (hs v) β hβ hβs Φ A.sec A'.sec U U' hs hs' hQ x y t k.1 k.2).trans (hex x y t k)
  have hui' : ∀ i, Integrable (fun t => conj (β t) * U t i) := fun i => hui (Sum.inl i)
  have hR : ∫ t, conj (β t) * ⟪v, U t⟫_ℂ = ∑ i, (∫ t, conj (β t) * U t i) * ⟪v, e i⟫_ℂ := by
    have hin : ∀ t, conj (β t) * ⟪v, U t⟫_ℂ = ∑ i, conj (β t) * U t i * ⟪v, e i⟫_ℂ := by
      intro t
      rw [inner_exp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hin]
    rw [integral_finset_sum _ fun i _ => (hui' i).mul_const _]
    simp only [integral_mul_const]
  have t1 : ∀ i, (c : ℂ) * ((∫ t, ui (Sum.inl i) t) * ∫ k, ∫ x, ∫ y, bi (Sum.inl i) x y k ∂fd μ₂ ∂fd μ₂ ∂κ) =
      (∫ t, conj (β t) * U t i) * ⟪v, e i⟫_ℂ := fun i => by
    have hb : (∫ k, ∫ x, ∫ y, bi (Sum.inl i) x y k ∂fd μ₂ ∂fd μ₂ ∂κ) =
      ∫ k : KG K (2 + 2), pm μ₂ (A.sec v) (A.sec (e i)) k k ∂κ := rfl
    have hu' : (∫ t, ui (Sum.inl i) t) = ∫ t, conj (β t) * U t i := rfl
    rw [hb, hu', ← hs₁ v (e i)]
    ring
  have t2 : ∀ j, (c : ℂ) * ((∫ t, ui (Sum.inr j) t) * ∫ k, ∫ x, ∫ y, bi (Sum.inr j) x y k ∂fd μ₂ ∂fd μ₂ ∂κ) = 0 := fun j => by
    have hb : (∫ k, ∫ x, ∫ y, bi (Sum.inr j) x y k ∂fd μ₂ ∂fd μ₂ ∂κ) =
      ∫ k : KG K (2 + 2), pm μ₂ (A.sec v) (A'.sec (e' j)) k k ∂κ := rfl
    rw [hb, hs₀, mul_zero, mul_zero]
  have hfive := five (fd μ₂) (fd μ₂) ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))) κ
    ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) _ hI
  rw [hE, parM, hfive, nest, key, hR, Fintype.sum_sum_type, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp only [t1, t2, Finset.sum_const_zero, add_zero]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctRep :
    ForAllC fun K _ _ μ _ _ _ _ _ D d d' A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → D.Hecke a → ∃ C : ℝ, ∀ φ, P φ = φ →
      ∃ (U : ℝ → Eu d) (U' : ℝ → Eu d'), Continuous U ∧ Continuous U' ∧ (∀ s, ‖U s‖ ≤ C * ‖φ‖ ∧ ‖U' s‖ ≤ C * ‖φ‖) ∧
        (∀ᵐ s : ℝ, Jd A.J (Rop μ a φ) s = U s) ∧ (∀ᵐ s : ℝ, Jd A'.J (Rop μ a φ) s = U' s) ∧
        ∀ z, ct 2 (rc μ a φ) z = secF A.sec U z + secF A'.sec U' z := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP ha
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  obtain ⟨C₁, hC₁, hb₁⟩ := adjBd μ μ₂ τ₁ τ₂ hp D d d' A A' a ha
  obtain ⟨C₂, hC₂, hb₂⟩ := adjBd μ μ₂ τ₂ τ₁ hp' D d' d A' A a ha
  refine ⟨max C₁ C₂, fun φ hφ => ?_⟩
  obtain ⟨κ, hκ⟩ := exK K
  obtain ⟨c, hU⟩ := (unf μ μ₂ κ).1
  obtain ⟨hs₁, hs₀⟩ := secIp K μ μ₂ τ₁ τ₂ hp D d d' A A' κ c hU
  obtain ⟨hkc, hrc⟩ := ctKv μ a
  obtain ⟨kc, hkcc, hkcs⟩ := hkc 2
  obtain ⟨hc₀, hr₀, hi₀, -, -⟩ := hrc φ
  have hf : Continuous (ct 2 (rc μ a φ)) := by
    have : ct 2 (rc μ a φ) = fun z => ⟪kc z, φ⟫_ℂ := funext fun z => (hkcs φ z).symm
    rw [this]
    exact hkcc.inner continuous_const
  choose v v' hv using ctMem K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha φ hφ
  let S : (Eu d × Eu d') →ₗ[ℂ] (G1 K (2 + 2) → ℂ) :=
    A.sec ∘ₗ LinearMap.fst ℂ _ _ + A'.sec ∘ₗ LinearMap.snd ℂ _ _
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    have e : A.sec x = A'.sec (-y) := by
      have : A.sec x + A'.sec y = 0 := hxy
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left this
    have h1 := hs₁ x x
    have h2 := hs₀ x (-y)
    rw [← e] at h2
    rw [h2, mul_zero] at h1
    have hx : x = 0 := inner_self_eq_zero.1 h1.symm
    have hy : y = 0 := by
      apply A'.inj
      have : A.sec x + A'.sec y = 0 := hxy
      rw [hx, map_zero, zero_add] at this
      rw [this, map_zero]
    rw [hx, hy]
    rfl
  obtain ⟨n, p, T, hT⟩ := ptInv S hS
  have hcv : Continuous fun s => (v s, v' s) := by
    have e : (fun s => (v s, v' s)) = fun s => T (fun i => ct 2 (rc μ a φ) (lv 1 1 (s - HH (p i)) * p i)) := by
      funext s
      rw [← hT (v s, v' s)]
      congr 1
      funext i
      exact (hv s (p i)).symm
    rw [e]
    exact T.continuous_of_finiteDimensional.comp (continuous_pi fun i => hf.comp (continuous_levi_unipotent_path K (p i) _))
  have hex : Continuous fun s : ℝ => Complex.exp (-2 * (s : ℂ)) := by fun_prop
  have hUc : Continuous fun s : ℝ => Complex.exp (-2 * (s : ℂ)) • v s := hex.smul hcv.fst
  have hUc' : Continuous fun s : ℝ => Complex.exp (-2 * (s : ℂ)) • v' s := hex.smul hcv.snd
  have hsF : ∀ {e : ℕ} (sec : Eu e →ₗ[ℂ] (G1 K (2 + 2) → ℂ)) (y : ℝ → Eu e) (z : G1 K (2 + 2)),
      secF sec (fun s : ℝ => Complex.exp (-2 * (s : ℂ)) • y s) z = sec (y (HH z)) z := by
    intro e sec y z
    rw [secF, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    simp
  have hQ : ∀ z, ct 2 (rc μ a φ) z = secF A.sec (fun s : ℝ => Complex.exp (-2 * (s : ℂ)) • v s) z +
      secF A'.sec (fun s : ℝ => Complex.exp (-2 * (s : ℂ)) • v' s) z := by
    intro z
    rw [hsF, hsF, ← hv (HH z) z, sub_self, (blkLaws (K := K)).2.2.1, one_mul]
  have hQ' : ∀ z, ct 2 (rc μ a φ) z = secF A'.sec (fun s : ℝ => Complex.exp (-2 * (s : ℂ)) • v' s) z +
      secF A.sec (fun s : ℝ => Complex.exp (-2 * (s : ℂ)) • v s) z := fun z => by rw [hQ, add_comm]
  have ae₁ := aeId (Jd A.J (Rop μ a φ)) _ hUc fun β w u hβ hβs hu => by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact ipSec μ μ₂ τ₁ τ₂ hp D d d' A A' κ c hU _ hc₀ hi₀ _ hr₀ _ _ hUc hUc' hQ β w u hβ hβs hu
  have ae₂ := aeId (Jd A'.J (Rop μ a φ)) _ hUc' fun β w u hβ hβs hu => by
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hU' : Unf μ μ₂ κ c := hU
    exact ipSec μ μ₂ τ₂ τ₁ hp' D d' d A' A κ c hU' _ hc₀ hi₀ _ hr₀ _ _ hUc' hUc hQ' β w u hβ hβs hu
  have hφ0 := norm_nonneg φ
  refine ⟨_, _, hUc, hUc', fun s => ⟨?_, ?_⟩, ae₁, ae₂, hQ⟩
  · refine bdAll _ hUc _ ?_ s
    filter_upwards [ae₁, hb₁ φ] with x h1 h2
    rw [← h1]
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hφ0)
  · refine bdAll _ hUc' _ ?_ s
    filter_upwards [ae₂, hb₂ φ] with x h1 h2
    rw [← h1]
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hφ0)
