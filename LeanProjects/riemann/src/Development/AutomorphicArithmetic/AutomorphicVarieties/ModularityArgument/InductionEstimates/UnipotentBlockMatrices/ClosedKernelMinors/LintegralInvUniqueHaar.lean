import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.GalLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.IsHilbertSchmidtOfAeEqDual

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lintegral_inv_unique_haar {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (U : Subgroup G) (ν ν' : Measure G) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ᵐ k ∂ν, k ∈ U) (h' : ∀ᵐ k ∂ν', k ∈ U) (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν)
    (hi' : ∀ k ∈ U, MeasurePreserving (k * ·) ν' ν') (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y ∂ν' = ∫⁻ x, F x⁻¹ ∂ν := by
  have e1 : ∫⁻ x, ∫⁻ y, F (x⁻¹ * y) ∂ν' ∂ν = ∫⁻ y, F y ∂ν' := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ y, F y ∂ν')]
    · simp
    · filter_upwards [h] with x hx
      exact (hi' _ (U.inv_mem hx)).lintegral_comp hF
  have e2 : ∫⁻ y, ∫⁻ x, F (x⁻¹ * y) ∂ν ∂ν' = ∫⁻ x, F x⁻¹ ∂ν := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ x, F x⁻¹ ∂ν)]
    · simp
    · filter_upwards [h'] with y hy
      have := (hi _ (U.inv_mem hy)).lintegral_comp (f := fun x => F x⁻¹) (hF.comp measurable_inv)
      simpa [mul_inv_rev] using this
  rw [← e1, ← e2]
  exact lintegral_lintegral_swap (hF.comp (measurable_fst.inv.mul measurable_snd)).aemeasurable

private theorem nu_pres {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (e : G1 K n ≃ₜ* G1 K n)
    (he : ∀ k, e k ∈ D.U ↔ k ∈ D.U) : MeasurePreserving e D.ν D.ν := by
  have := D.prob
  have hm : Measurable e := e.continuous.measurable
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have : IsProbabilityMeasure (D.ν.map e) := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hp : MeasurePreserving e D.ν (D.ν.map e) := ⟨hm, rfl⟩
  have hs : ∀ᵐ k ∂(D.ν.map e), k ∈ D.U := by
    rw [hemb.ae_map_iff]
    filter_upwards [D.supp] with k hk using (he k).2 hk
  have hi : ∀ k ∈ D.U, MeasurePreserving (k * ·) (D.ν.map e) (D.ν.map e) := by
    intro k hk
    have hk' : e.symm k ∈ D.U := (he _).1 (by simpa using hk)
    refine ⟨measurable_const_mul k, ?_⟩
    rw [Measure.map_map (measurable_const_mul k) hm]
    conv_rhs => rw [← (D.inv _ hk').map_eq, Measure.map_map hm (measurable_const_mul _)]
    congr 1
    funext x
    simp
  refine ⟨hm, Measure.ext_of_lintegral _ fun F hF => ?_⟩
  rw [lintegral_inv_unique_haar D.U D.ν _ D.supp hs D.inv hi F hF, lintegral_inv_unique_haar D.U D.ν _ D.supp D.supp D.inv D.inv F hF]

private theorem fix_tw {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    (D : TypeDat K n) (θ : Twist μ) (hs : Stable D θ) (f : G1 K n → ℂ) (hf : D.Fix f) :
    D.Fix fun x => f (θ.e.symm x) := by
  intro g
  have hemb : MeasurableEmbedding θ.e := θ.e.toHomeomorph.measurableEmbedding
  rw [← (nu_pres D θ.e hs.1).integral_comp hemb]
  refine Eq.trans (integral_congr_ae ?_) (hf (θ.e.symm g))
  filter_upwards [D.supp] with k hk
  simp [hs.2 k hk]

private theorem reps_uniq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {v w : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w φ) : v = w := by
  refine Lp.ext ?_
  have h : ∀ᵐ y ∂μ, (v : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) = (w : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) := by
    filter_upwards [hv, hw] with y a b using a.trans b.symm
  have hm : MeasurableSet {y | (v : RightCosetSpace (Gam K n) → ℂ) y = (w : RightCosetSpace (Gam K n) → ℂ) y} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable (Lp.stronglyMeasurable w).measurable
  exact (ae_map_iff (measurable_mk (Gam K n)).aemeasurable hm).2 (ae_restrict_of_ae h)

private theorem reps_tw {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    (θ : Twist μ) {v : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) : Reps μ (θ.U v) fun x => φ (θ.e.symm x) := by
  have hp : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have h1 := hp.quasiMeasurePreserving.ae hv
  have h2 := (quasiMeasurePreserving_mk (Gam K n) μ).ae (θ.U_spec v)
  filter_upwards [h1, h2] with y a b
  rw [b, ← a]
  congr 1
  obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K n)).1 (Quotient.out_eq (mk (Gam K n) y))
  rw [← hγ]
  have : θ.e.symm (γ • y) = θ.e.symm γ * θ.e.symm y := map_mul _ _ _
  rw [this]
  exact mk_mul_of_mem ((θ.mem_gam _).1 (by simp)) _

private theorem th_tw {K : Type} [Field K] [NumberField K] (e : G1 K (2 + 2) ≃ₜ* G1 K (2 + 2))
    (hG : ∀ g, e g ∈ Gam K (2 + 2) ↔ g ∈ Gam K (2 + 2)) (hP : ∀ γ, e γ ∈ PK K ↔ γ ∈ PK K)
    (F : G1 K (2 + 2) → ℂ) (hF : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (g : G1 K (2 + 2)) :
    th (fun x => F (e.symm x)) g = th F (e.symm g) := by
  have hm : ∀ γ : Gam K (2 + 2), (γ : G1 K (2 + 2)) ∈ PK K ↔ γ ∈ ParΓ K 2 2 := fun γ =>
    Subgroup.mem_map_iff_mem (f := (Gam K (2 + 2)).subtype) Subtype.val_injective
  let ε : Gam K (2 + 2) ≃ Gam K (2 + 2) := e.toEquiv.subtypeEquiv fun a => (hG a).symm
  have hε : ∀ a, ((ε a : Gam K (2 + 2)) : G1 K (2 + 2)) = e a := fun a => rfl
  let Q : Cos K ≃ Cos K := Quotient.congr ε fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← hm, ← hm, ← hP]
    simp [hε]
  unfold th
  rw [← finsum_comp_equiv Q]
  refine finsum_congr fun q => ?_
  have h1 : Q q = Quotient.mk _ (ε q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have h2 : (QuotientGroup.rightRel (ParΓ K 2 2)) (ε q.out) (Q q).out := by
    refine Quotient.exact ?_
    rw [Quotient.out_eq, h1]
  rw [QuotientGroup.rightRel_apply, ← hm] at h2
  have h3 := (hP (e.symm _)).1 (by rw [e.apply_symm_apply]; exact h2)
  rw [← hF _ h3 (_ * e.symm g)]
  congr 1
  simp [hε, mul_assoc]

private theorem sec_tw {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} (i₁ : CuspIrr μ₂ τ₁) (i₂ : CuspIrr μ₂ τ₂)
    {D : TypeDat K (2 + 2)} {σ : K ≃+* K} {θ : Twist μ} {θ₂ : Twist μ₂} (h : UpperTheory.ConvolutionTheory.K.IsGal σ θ)
    (h₂ : UpperTheory.ConvolutionTheory.K.IsGal σ θ₂) (hs : Stable D θ) (m₁ : τ₁.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₂)
    (m₂ : τ₂.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₁) (f : G1 K (2 + 2) → ℂ) (hf : IsSec τ₁ τ₂ f ∧ D.Fix f) :
    IsSec τ₂ τ₁ (fun x => f (θ.e.symm x)) ∧ D.Fix fun x => f (θ.e.symm x) := by
  have hx := fix_tw D θ hs f hf.2
  obtain ⟨g1, g2, -⟩ := galLaws μ μ₂ σ θ θ₂ h h₂
  have g3 : ∀ a b t, θ.e.symm (lv a b t) = lv (θ₂.e.symm a) (θ₂.e.symm b) t := fun a b t => by
    apply θ.e.injective
    simp [g1]
  obtain ⟨c, ⟨C, hC⟩, hn, hr, hl⟩ := (secCrit μ₂ τ₁ τ₂ D i₁ i₂ f hf.2).1 hf.1
  refine ⟨(secCrit μ₂ τ₂ τ₁ D i₂ i₁ _ hx).2 ⟨c.comp θ.e.symm.continuous, ⟨C, fun g => hC _⟩, fun X g => ?_, fun t g => ?_,
    fun g => ⟨fun b => ?_, fun a => ?_⟩⟩, hx⟩
  · obtain ⟨Y, hY⟩ := (g2 X).2
    simp only [map_mul, hY, hn]
  · simp only [map_mul, g3, map_one, hr]
  · obtain ⟨v, hv, hv'⟩ := (hl (θ.e.symm g)).1 (θ₂.e.symm b)
    refine ⟨θ₂.U v, m₁ ▸ Submodule.mem_map_of_mem hv, ?_⟩
    simpa only [map_mul, g3] using reps_tw θ₂ hv'
  · obtain ⟨v, hv, hv'⟩ := (hl (θ.e.symm g)).2 (θ₂.e.symm a)
    refine ⟨θ₂.U v, m₂ ▸ Submodule.mem_map_of_mem hv, ?_⟩
    simpa only [map_mul, g3] using reps_tw θ₂ hv'

private theorem lin_tw {K : Type} [Field K] [NumberField K] {μ : Measure (G1 K (2 + 2))}
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ ρ₁ ρ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d d' : ℕ} (A : Line μ τ₁ τ₂ D d)
    (A' : Line μ ρ₁ ρ₂ D d') (e : G1 K (2 + 2) ≃ G1 K (2 + 2))
    (h : ∀ f, IsSec τ₁ τ₂ f ∧ D.Fix f → IsSec ρ₁ ρ₂ (fun x => f (e x)) ∧ D.Fix fun x => f (e x)) :
    ∃ s : Eu d →ₗ[ℂ] Eu d', Function.Injective s ∧ ∀ v, A'.sec (s v) = fun x => A.sec v (e x) := by
  obtain ⟨r, hr⟩ := A'.sec.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 A'.inj)
  have key : ∀ v, A'.sec ((r ∘ₗ LinearMap.funLeft ℂ ℂ e ∘ₗ A.sec) v) = fun x => A.sec v (e x) := fun v => by
    obtain ⟨w, hw⟩ := (A'.onto _).2 (h _ ((A.onto _).1 ⟨v, rfl⟩))
    have : (r ∘ₗ LinearMap.funLeft ℂ ℂ e ∘ₗ A.sec) v = r (A'.sec w) := by rw [hw]; rfl
    rw [this, ← hw]
    exact congrArg _ (LinearMap.congr_fun hr w)
  refine ⟨_, fun v w hvw => A.inj (funext fun x => ?_), key⟩
  have := congrFun ((key v).symm.trans ((congrArg A'.sec hvw).trans (key w))) (e.symm x)
  simpa using this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.convU :
    ConvUC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' σ θ θ₂ h h₂ hs m₁ m₂
  obtain ⟨s, hsi, hsec⟩ := lin_tw A A' θ.e.symm.toEquiv (sec_tw hp.irr₁ hp.irr₂ h h₂ hs m₁ m₂)
  obtain ⟨s', hsi', -⟩ := lin_tw A' A θ.e.symm.toEquiv (sec_tw hp.irr₂ hp.irr₁ h h₂ hs m₂ m₁)
  have hd : Module.finrank ℂ (Eu d) = Module.finrank ℂ (Eu d') :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hsi) (LinearMap.finrank_le_finrank_of_injective hsi')
  obtain ⟨-, -, -, gP, gH⟩ := galLaws μ μ₂ σ θ θ₂ h h₂
  obtain ⟨U, hU, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary K _ μ θ
  let S : L (Eu d) →L[ℂ] L (Eu d') := (LinearMap.toContinuousLinearMap s).compLpL 2 volume
  have hS : ∀ u, ∀ᵐ x : ℝ, S u x = s (u x) := fun u => (LinearMap.toContinuousLinearMap s).coeFn_compLpL u
  have hcomm : θ.U ∘L A.J.toContinuousLinearMap = A'.J.toContinuousLinearMap ∘L S := by
    refine ContinuousLinearMap.ext_on (denseCc d).1 ?_
    rintro u ⟨β, v, hβ, hβc, hu⟩
    have hv := (A.onto _).1 ⟨v, rfl⟩
    have hb := (bfFun _ β (secFun μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ hv.1 hv.2) hβ hβc).1.rat
    have r1 := reps_tw θ (A.spec β v u hβ hβc hu)
    have r2 := A'.spec β (s v) (S u) hβ hβc (by
      filter_upwards [hS u, hu] with x a b
      rw [a, b, map_smul])
    refine reps_uniq r1 ?_
    have : theta β (A'.sec (s v)) = fun x => theta β (A.sec v) (θ.e.symm x) := by
      funext x
      rw [theta_eq, theta_eq, ← th_tw θ.e θ.mem_gam gP _ hb, hsec]
      congr 1
      funext y
      have : HP 2 2 (θ.e.symm y) = HP 2 2 y := by simpa using (gH (θ.e.symm y)).symm
      simp only [bf, this]
      rfl
    rw [← this]
    exact r2
  have hc : ∀ (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, v x = s (u x)) → θ.U (A.J u) = A'.J v := fun u v huv => by
    have : v = S u := Lp.ext (by filter_upwards [huv, hS u] with x a b using a.trans b.symm)
    rw [this]
    exact congrArg (fun T : L (Eu d) →L[ℂ] L2 μ => T u) hcomm
  have hn : ∀ v, ‖s v‖ = ‖v‖ := fun v => by
    have hI : (volume : Measure ℝ) (Icc 0 1) ≠ ∞ := by simp
    have := hc (indicatorConstLp 2 measurableSet_Icc hI v) (indicatorConstLp 2 measurableSet_Icc hI (s v)) (by
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Icc) (hμs := hI) (c := v),
        indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Icc) (hμs := hI) (c := s v)] with x a b
      rw [a, b]
      by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx])
    have h2 := congrArg norm this
    rw [← hU] at h2
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map,
      LinearIsometry.norm_map] at h2
    rw [norm_indicatorConstLp (by simp) (by simp), norm_indicatorConstLp (by simp) (by simp)] at h2
    simpa using h2.symm
  exact ⟨LinearIsometry.toLinearIsometryEquiv ⟨s, hn⟩ hd, fun v x => congrFun (hsec v) x, hc⟩
