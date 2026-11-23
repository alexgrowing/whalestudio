import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TChiSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.IwaInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem disint {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (H : G → ℝ) (hH : Continuous H) (r : ℝ → G)
    (hr : Continuous r) (hrH : ∀ t g, H (r t * g) = t + H g) (φ : G → E) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ κ : ℝ → E, Continuous κ ∧ HasCompactSupport κ ∧
      ∀ χ : ℝ → ℂ, Continuous χ → ∫ g, χ (H g) • φ g ∂μ = ∫ s, χ s • κ s := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let ρ : ℝ → ℂ := fun t => (b.normed volume t : ℝ)
  have hρ : Continuous ρ := Complex.continuous_ofReal.comp b.continuous_normed
  have hρc : HasCompactSupport ρ := b.hasCompactSupport_normed.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  have hρ1 : ∀ x : ℝ, ∫ t, ρ (x - t) = 1 := fun x => by
    rw [integral_sub_left_eq_self ρ volume x]
    simp only [ρ]
    rw [integral_complex_ofReal, b.integral_normed]
    rfl
  let h₁ : ℝ × G ≃ₜ ℝ × G :=
    { toFun := fun p => (p.1, r p.1 * p.2), invFun := fun p => (p.1, (r p.1)⁻¹ * p.2)
      left_inv := fun p => by simp, right_inv := fun p => by simp
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  let h₂ : ℝ × G ≃ₜ ℝ × G :=
    { toFun := fun p => (p.1 - H p.2, p.2), invFun := fun p => (p.1 + H p.2, p.2)
      left_inv := fun p => by simp, right_inv := fun p => by simp
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  let Ψ : (ℝ → ℂ) → ℝ × G → E := fun χ p => ρ (H p.2 - p.1) • χ (H p.2) • φ p.2
  have hΨ : ∀ χ, Continuous χ → Continuous (Ψ χ) := fun χ hχ => by
    simp only [Ψ]
    fun_prop
  have hΨc : ∀ χ, HasCompactSupport (Ψ χ) := fun χ => by
    refine HasCompactSupport.intro (((hφc.isCompact.prod hρc.isCompact).image
      (f := fun q : G × ℝ => (H q.1 - q.2, q.1)) (by fun_prop))) fun p hp => by_contra fun h => hp ?_
    refine ⟨(p.2, H p.2 - p.1), ⟨subset_tsupport _ fun h0 => h ?_, subset_tsupport _ fun h0 => h ?_⟩, by simp⟩
    · simp only [Ψ]
      rw [show φ p.2 = 0 from h0, smul_zero, smul_zero]
    · simp only [Ψ]
      rw [show ρ (H p.2 - p.1) = 0 from h0, zero_smul]
  have hB : ∀ χ s g, Ψ χ (h₁ (h₂ (s, g))) = χ s • Ψ 1 (h₁ (h₂ (s, g))) := fun χ s g => by
    change ρ _ • χ (H (r (s - H g) * g)) • _ = χ s • ρ _ • (1 : ℂ) • _
    rw [hrH, sub_add_cancel, one_smul, smul_comm]
  have hc1 : Continuous fun p => Ψ 1 (h₁ (h₂ p)) := (hΨ 1 continuous_const).comp (h₁.continuous.comp h₂.continuous)
  have hs1 : HasCompactSupport fun p => Ψ 1 (h₁ (h₂ p)) := ((hΨc 1).comp_homeomorph h₁).comp_homeomorph h₂
  refine ⟨fun s => ∫ g, Ψ 1 (h₁ (h₂ (s, g))) ∂μ, ?_, ?_, fun χ hχ => ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := μ) (f := fun s g => Ψ 1 (h₁ (h₂ (s, g)))) hc1
      (hs1.isCompact.image continuous_snd)
    refine this.congr fun s => setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => by_contra fun h => hg ?_
    exact ⟨(s, g), subset_tsupport _ h, rfl⟩
  · refine HasCompactSupport.intro (hs1.isCompact.image continuous_fst) fun s hs => ?_
    refine integral_eq_zero_of_ae (Eventually.of_forall fun g => by_contra fun h => hs ?_)
    exact ⟨(s, g), subset_tsupport _ h, rfl⟩
  · have i0 : Integrable (Ψ χ) ((volume : Measure ℝ).prod μ) := (hΨ χ hχ).integrable_of_hasCompactSupport (hΨc χ)
    have i1 : Integrable (fun p => Ψ χ (h₁ p)) ((volume : Measure ℝ).prod μ) :=
      ((hΨ χ hχ).comp h₁.continuous).integrable_of_hasCompactSupport ((hΨc χ).comp_homeomorph h₁)
    have i2 : Integrable (fun p => Ψ χ (h₁ (h₂ p))) ((volume : Measure ℝ).prod μ) :=
      ((hΨ χ hχ).comp (h₁.continuous.comp h₂.continuous)).integrable_of_hasCompactSupport
        (((hΨc χ).comp_homeomorph h₁).comp_homeomorph h₂)
    calc ∫ g, χ (H g) • φ g ∂μ = ∫ g, ∫ t, Ψ χ (t, g) ∂volume ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun g => ?_)
          simp only [Ψ]
          rw [integral_smul_const, hρ1, one_smul]
      _ = ∫ t, ∫ g, Ψ χ (t, g) ∂μ := (integral_integral_swap (f := fun t g => Ψ χ (t, g)) i0).symm
      _ = ∫ t, ∫ g, Ψ χ (h₁ (t, g)) ∂μ := integral_congr_ae (Eventually.of_forall fun t =>
          (integral_mul_left_eq_self (fun g => Ψ χ (t, g)) (r t)).symm)
      _ = ∫ g, ∫ t, Ψ χ (h₁ (t, g)) ∂volume ∂μ := integral_integral_swap (f := fun t g => Ψ χ (h₁ (t, g))) i1
      _ = ∫ g, ∫ s, Ψ χ (h₁ (h₂ (s, g))) ∂volume ∂μ := integral_congr_ae (Eventually.of_forall fun g =>
          (integral_sub_right_eq_self (fun t => Ψ χ (h₁ (t, g))) (H g)).symm)
      _ = ∫ s, ∫ g, Ψ χ (h₁ (h₂ (s, g))) ∂μ := (integral_integral_swap (f := fun s g => Ψ χ (h₁ (h₂ (s, g)))) i2).symm
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun s => ?_)
          simp only [hB χ s]
          rw [integral_smul]

private theorem coords {X : Type*} {d : ℕ} (S : Eu d →ₗ[ℂ] (X → ℂ)) (hS : Function.Injective S) :
    ∃ c : Fin d → X →₀ ℂ, ∀ (v : Eu d) (i : Fin d), v i = ∑ x ∈ (c i).support, c i x * S v x := by
  have h : Submodule.span ℂ (range fun x : X => (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ S) = ⊤ :=
    Submodule.span_eq_top_of_ne_zero fun z hz => by
      obtain ⟨x, hx⟩ := Function.ne_iff.1 ((map_ne_zero_iff S hS).2 hz)
      exact ⟨_, ⟨x, rfl⟩, hx⟩
  have h2 : ∀ i : Fin d, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ S)) =
      (EuclideanSpace.proj i : Eu d →L[ℂ] ℂ).toLinearMap := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (h ▸ Submodule.mem_top)
  choose c hc using h2
  refine ⟨c, fun v i => ?_⟩
  have := LinearMap.congr_fun (hc i) v
  simpa [Finsupp.sum, LinearMap.sum_apply] using this.symm

private theorem assemble0 {d : ℕ} (γ : Fin d → ℝ → Eu d →L[ℂ] ℂ) (hγ : ∀ i, Continuous (γ i))
    (hγc : ∀ i, HasCompactSupport (γ i)) : ∃ β : ℝ → Eu d →L[ℂ] Eu d, Ker β ∧ ∀ s v i, β s v i = γ i s v := by
  refine ⟨fun s => ∑ i, (γ i s).smulRight (EuclideanSpace.single i (1 : ℂ)), ⟨continuous_clm_apply.2 fun v => ?_, ?_⟩,
    fun s v i => ?_⟩
  · simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
    refine continuous_finset_sum _ fun i _ => ?_
    have : Continuous fun s => γ i s v := (hγ i).clm_apply continuous_const
    fun_prop
  · refine HasCompactSupport.intro (isCompact_iUnion fun i => (hγc i).isCompact) fun s hs => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have : γ i s = 0 := by_contra fun h => hs (mem_iUnion.2 ⟨i, subset_tsupport _ h⟩)
    rw [this]
    ext1
    simp
  · simp [ContinuousLinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]

private theorem int_app {Y E F : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace E] [CompleteSpace F] (T : E →L[ℂ] F) {χ : Y → ℂ} {φ : Y → E} (hχ : Continuous χ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : T (∫ y, χ y • φ y ∂μ) = ∫ y, χ y • T (φ y) ∂μ := by
  have hi : Integrable (fun y => χ y • φ y) μ := (hχ.smul hφ).integrable_of_hasCompactSupport hc.smul_left
  rw [← T.integral_comp_comm hi]
  simp only [map_smul]

private theorem assemble {X : Type*} {d : ℕ} (S : Eu d →ₗ[ℂ] (X → ℂ)) (hS : Function.Injective S)
    (κ : X → ℝ → Eu d →L[ℂ] ℂ) (hκ : ∀ x, Continuous (κ x)) (hκc : ∀ x, HasCompactSupport (κ x)) :
    ∃ β : ℝ → Eu d →L[ℂ] Eu d, Ker β ∧ ∀ (χ : ℝ → ℂ) (v w : Eu d), Continuous χ →
      (∀ x, S w x = ∫ s, χ s * κ x s v) → w = ∫ s, χ s • β s v := by
  obtain ⟨c, hc⟩ := coords S hS
  obtain ⟨β, hβ, hβv⟩ := assemble0 (fun i s => ∑ x ∈ (c i).support, c i x • κ x s)
    (fun i => continuous_finset_sum _ fun x _ => by have := hκ x; fun_prop) fun i => by
      refine HasCompactSupport.intro ((c i).support.isCompact_biUnion fun x _ => (hκc x).isCompact) fun s hs => ?_
      refine Finset.sum_eq_zero fun x hx => ?_
      have : κ x s = 0 := by_contra fun h => hs (mem_iUnion₂.2 ⟨x, hx, subset_tsupport _ h⟩)
      rw [this, smul_zero]
  refine ⟨β, hβ, fun χ v w hχ hw => ?_⟩
  ext i
  have h1 : Continuous fun s => β s v := hβ.1.clm_apply continuous_const
  have h2 : HasCompactSupport fun s => β s v := hβ.2.comp_left (g := fun T : Eu d →L[ℂ] Eu d => T v) rfl
  have e := int_app volume (EuclideanSpace.proj i : Eu d →L[ℂ] ℂ) hχ h1 h2
  have hI : ∀ x, Integrable fun s => c i x * (χ s * κ x s v) := fun x => by
    have h3 : Continuous fun s => κ x s v := (hκ x).clm_apply continuous_const
    have h4 : HasCompactSupport fun s => κ x s v := (hκc x).comp_left (g := fun T : Eu d →L[ℂ] ℂ => T v) rfl
    exact ((hχ.mul h3).integrable_of_hasCompactSupport h4.mul_left).const_mul _
  refine Eq.trans ?_ e.symm
  rw [hc w i]
  simp only [hw, ← integral_const_mul]
  rw [← integral_finset_sum _ fun x _ => hI x]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  change _ = χ s * β s v i
  rw [hβv, ContinuousLinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tChiKer :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)) {d : ℕ} (A : Line μ τ₁ τ₂ D d), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ → ∀ a : CC K (2 + 2), D.Hecke a →
      ∃ β : ℝ → Eu d →L[ℂ] Eu d, Ker β ∧ ∀ (χ : ℝ → ℂ) (v : Eu d), Continuous χ → tChi μ a χ (A.sec v) = A.sec (∫ s, χ s • β s v) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ D d A h₁ h₂ a ha
  obtain ⟨hH1, -, -, hHc, -⟩ := hpSpec (K := K)
  obtain ⟨-, -, -, hlv, -⟩ := blkLaws (K := K)
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  let ev : G1 K (2 + 2) → Eu d →L[ℂ] ℂ := fun g =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj g : (G1 K (2 + 2) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ A.sec)
  have hev : Continuous ev := continuous_clm_apply.2 fun v => (hsec v).1.cont
  have hr : Continuous fun t : ℝ => lv (1 : G1 K 2) 1 t := by
    have : Continuous fun t : ℝ => ((1 : G1 K 2), (1 : G1 K 2), t) := by fun_prop
    simpa only [Function.comp_def] using hlv.comp this
  have key : ∀ x : G1 K (2 + 2), ∃ κ : ℝ → Eu d →L[ℂ] ℂ, Continuous κ ∧ HasCompactSupport κ ∧
      ∀ (χ : ℝ → ℂ) (v : Eu d), Continuous χ → tChi μ a χ (A.sec v) x = ∫ s, χ s * κ s v := fun x => by
    have hac : Continuous fun g => a (x⁻¹ * g) := a.continuous.comp (continuous_const.mul continuous_id)
    have has : HasCompactSupport fun g => a (x⁻¹ * g) := a.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
    have hH : Continuous fun g => HH g - HH x := hHc.sub continuous_const
    have hφ : Continuous fun g => a (x⁻¹ * g) • Complex.exp (2 * ((HH g - HH x : ℝ) : ℂ)) • ev g :=
      hac.smul ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hH))).smul hev)
    have hφc : HasCompactSupport fun g => a (x⁻¹ * g) • Complex.exp (2 * ((HH g - HH x : ℝ) : ℂ)) • ev g := has.smul_right
    obtain ⟨κ, hκ, hκc, h⟩ := disint μ (fun g => HH g - HH x) hH (fun t => lv 1 1 t) hr (fun t g => by
      have := hH1 0 1 1 t g
      rw [show (nn 0 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul] at this
      rw [this, add_sub_assoc]) _ hφ hφc
    refine ⟨κ, hκ, hκc, fun χ v hχ => ?_⟩
    have h3 := congrArg (ContinuousLinearMap.apply ℂ ℂ v) (h χ hχ)
    rw [int_app μ _ (χ := fun g => χ (HH g - HH x)) (hχ.comp hH) hφ hφc, int_app volume _ hχ hκ hκc] at h3
    simp only [ContinuousLinearMap.apply_apply] at h3
    refine Eq.trans ?_ h3
    unfold tChi
    rw [← integral_mul_left_eq_self _ x⁻¹]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [mul_inv_cancel_left, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have : ev g v = A.sec v g := rfl
    rw [this]
    ring
  choose κ hκ hκc hκe using key
  obtain ⟨β, hβ, h⟩ := assemble A.sec A.inj κ hκ hκc
  refine ⟨β, hβ, fun χ v hχ => ?_⟩
  obtain ⟨w, hw⟩ := (A.onto _).2 (tChiSec μ μ₂ τ₁ τ₂ D h₁ h₂ a χ (A.sec v) ha hχ (hsec v).1 (hsec v).2)
  rw [← hw, ← h χ v w hχ fun x => by rw [hw, hκe x χ v hχ]]
