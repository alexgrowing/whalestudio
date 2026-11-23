import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem hasSum_integral_smul_of_partition {X Γ E : Type} [MeasurableSpace X] [Countable Γ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) (w : Γ → X → ℝ)
    (hw : ∀ γ, Measurable (w γ)) (hw0 : ∀ γ x, 0 ≤ w γ x)
    (hw1 : ∀ x, HasSum (fun γ => w γ x) 1) (F : X → E) (hF : Integrable F μ) :
    (∀ γ, Integrable (fun x => w γ x • F x) μ) ∧
      HasSum (fun γ => ∫ x, w γ x • F x ∂μ) (∫ x, F x ∂μ) := by
  have hle : ∀ γ x, w γ x ≤ 1 := fun γ x =>
    le_hasSum (hw1 x) γ (fun j _ => hw0 j x)
  have hnorm : ∀ γ x, ‖w γ x • F x‖ = w γ x * ‖F x‖ := fun γ x => by
    rw [norm_smul, Real.norm_of_nonneg (hw0 γ x)]
  have hmeas : ∀ γ, AEStronglyMeasurable (fun x => w γ x • F x) μ := fun γ =>
    (hw γ).aestronglyMeasurable.smul hF.aestronglyMeasurable
  refine ⟨fun γ => hF.mono (hmeas γ) (Eventually.of_forall fun x => ?_), ?_⟩
  · rw [hnorm]
    exact mul_le_of_le_one_left (norm_nonneg _) (hle γ x)
  refine hasSum_integral_of_dominated_convergence (fun γ x => w γ x * ‖F x‖) hmeas
    (fun γ => Eventually.of_forall fun x => (hnorm γ x).le)
    (Eventually.of_forall fun x => ((hw1 x).mul_right ‖F x‖).summable) ?_ ?_
  · have : (fun x => ∑' γ, w γ x * ‖F x‖) = fun x => ‖F x‖ := by
      funext x
      rw [((hw1 x).mul_right ‖F x‖).tsum_eq, one_mul]
    rw [this]
    exact hF.norm
  · exact Eventually.of_forall fun x => by simpa using (hw1 x).smul_const (F x)

theorem integrable_tsum_of_summable_norm_integral {ι Y : Type} [Countable ι]
    [MeasurableSpace Y] (μ : Measure Y) (F : ι → Y → ℂ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ := by
  have hm : AEStronglyMeasurable (fun y => ∑' i, F i y) μ :=
    (AEMeasurable.tsum fun i => (hF i).aemeasurable).aestronglyMeasurable
  have hle : ∫⁻ y, ‖∑' i, F i y‖ₑ ∂μ ≤ ENNReal.ofReal (∑' i, ∫ y, ‖F i y‖ ∂μ) := by
    calc ∫⁻ y, ‖∑' i, F i y‖ₑ ∂μ ≤ ∫⁻ y, ∑' i, ‖F i y‖ₑ ∂μ :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ y, ‖F i y‖ₑ ∂μ := lintegral_tsum fun i => (hF i).aemeasurable.enorm
      _ = ∑' i, ENNReal.ofReal (∫ y, ‖F i y‖ ∂μ) :=
          tsum_congr fun i => (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg
          (fun i => integral_nonneg fun y => norm_nonneg _) hs).symm
  exact ⟨hm, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩

theorem abstract_double_coset_adjoint : ∀ (G X Γ ι κ : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X] (μ : Measure X) [SMulInvariantMeasure G X μ] [Group Γ] [Countable Γ] [Fintype ι] [Fintype κ] (φ : Γ →* G) (ρ : X → ℝ) (β : ι → G) (α : κ → G) (e : Γ × ι ≃ κ × Γ) (P : ι → X → ℂ) (Q : κ → X → ℂ), Measurable ρ → (∀ x, 0 ≤ ρ x) → (∀ x, HasSum (fun γ : Γ => ρ (φ γ • x)) 1) → (∀ p, φ p.1 * β p.2 = α (e p).1 * φ (e p).2) → (∀ p x, P p.2 x = Q (e p).1 (φ (e p).2 • x)) → (∀ i, Integrable (fun x => (ρ x : ℂ) * P i x) μ) → (∀ j, AEStronglyMeasurable (Q j) μ) → (∀ j, Integrable (fun x => (ρ x : ℂ) * Q j ((α j)⁻¹ • x)) μ) ∧ ∑ i, ∫ x, (ρ x : ℂ) * P i x ∂μ = ∑ j, ∫ x, (ρ x : ℂ) * Q j ((α j)⁻¹ • x) ∂μ := by
  intro G X Γ ι κ _ _ _ _ μ _ _ _ _ _ φ ρ β α e P Q hρm hρ0 hρ1 he hPQ hPi _

  set wP : ι → Γ → X → ℝ := fun i γ x => ρ (φ γ • β i • x) with hwP
  set wQ : κ → Γ → X → ℝ := fun j γ y => ρ ((φ γ)⁻¹ • (α j)⁻¹ • y) with hwQ
  set FP : ι → X → ℂ := fun i x => (ρ x : ℂ) * P i x with hFP
  set FQ : κ → X → ℂ := fun j y => (ρ y : ℂ) * Q j ((α j)⁻¹ • y) with hFQ
  have hwPm : ∀ i γ, Measurable (wP i γ) := fun i γ =>
    hρm.comp ((measurable_id.const_smul (β i)).const_smul (φ γ))
  have hwQm : ∀ j γ, Measurable (wQ j γ) := fun j γ =>
    hρm.comp ((measurable_id.const_smul (α j)⁻¹).const_smul (φ γ)⁻¹)
  have hwP0 : ∀ i γ x, 0 ≤ wP i γ x := fun _ _ _ => hρ0 _
  have hwQ0 : ∀ j γ x, 0 ≤ wQ j γ x := fun _ _ _ => hρ0 _
  have hwP1 : ∀ i x, HasSum (fun γ => wP i γ x) 1 := fun i x => hρ1 (β i • x)
  have hwQ1 : ∀ j y, HasSum (fun γ => wQ j γ y) 1 := fun j y => by
    have h := (Equiv.inv Γ).hasSum_iff.2 (hρ1 ((α j)⁻¹ • y))
    simpa [Function.comp_def, map_inv] using h

  have hpt : ∀ (q : κ × Γ) (x : X),
      wQ q.1 q.2 ((α q.1 * φ q.2) • x) • FQ q.1 ((α q.1 * φ q.2) • x) =
        wP (e.symm q).2 (e.symm q).1 x • FP (e.symm q).2 x := by
    intro q x
    have h1 := he (e.symm q)
    have h2 := hPQ (e.symm q) x
    simp only [Equiv.apply_symm_apply] at h1 h2
    have hx1 : (φ q.2)⁻¹ • (α q.1)⁻¹ • (α q.1 * φ q.2) • x = x := by
      rw [smul_smul, smul_smul, ← mul_assoc, mul_assoc _ (α q.1)⁻¹, inv_mul_cancel, mul_one,
        inv_mul_cancel, one_smul]
    have hx2 : (α q.1)⁻¹ • (α q.1 * φ q.2) • x = φ q.2 • x := by
      rw [smul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hx3 : (α q.1 * φ q.2) • x = φ (e.symm q).1 • β (e.symm q).2 • x := by
      rw [← h1, mul_smul]
    simp only [hwQ, hwP, hFQ, hFP, hx1, hx2, h2, inv_smul_smul]
    rw [hx3, Complex.real_smul, Complex.real_smul]
    ring

  have hPpart := fun i => hasSum_integral_smul_of_partition μ (wP i) (hwPm i) (hwP0 i) (hwP1 i)
    (FP i) (hPi i)
  have hPnorm := fun i => hasSum_integral_smul_of_partition μ (wP i) (hwPm i) (hwP0 i) (hwP1 i)
    (fun x => ‖FP i x‖) (hPi i).norm
  have hnP : ∀ i γ x, ‖wP i γ x • FP i x‖ = wP i γ x • ‖FP i x‖ := fun i γ x => by
    rw [norm_smul, Real.norm_of_nonneg (hwP0 i γ x), smul_eq_mul]
  let a : Γ × ι → ℝ := fun p => ∫ x, ‖wP p.2 p.1 x • FP p.2 x‖ ∂μ
  let t : Γ × ι → ℂ := fun p => ∫ x, wP p.2 p.1 x • FP p.2 x ∂μ
  have ha0 : 0 ≤ a := fun p => integral_nonneg fun x => norm_nonneg _
  have haP : ∀ i, HasSum (fun γ => a (γ, i)) (∫ x, ‖FP i x‖ ∂μ) := fun i => by
    simpa only [a, hnP] using (hPnorm i).2
  have hsa : Summable a := by
    rw [summable_prod_of_nonneg ha0]
    refine ⟨fun γ => Summable.of_finite, ?_⟩
    simp only [tsum_fintype]
    exact summable_sum fun i _ => (haP i).summable
  have hst : Summable t :=
    Summable.of_norm_bounded hsa fun p => norm_integral_le_integral_norm _

  have hcv : ∀ q : κ × Γ, (fun x => wQ q.1 q.2 ((α q.1 * φ q.2) • x) •
      FQ q.1 ((α q.1 * φ q.2) • x)) = fun x => wP (e.symm q).2 (e.symm q).1 x • FP (e.symm q).2 x :=
    fun q => funext (hpt q)
  have hta : ∀ q : κ × Γ, t (e.symm q) = ∫ y, wQ q.1 q.2 y • FQ q.1 y ∂μ := fun q => by
    rw [← integral_smul_eq_self (fun y => wQ q.1 q.2 y • FQ q.1 y) (g := α q.1 * φ q.2)]
    exact congrArg (fun f => ∫ x, f x ∂μ) (hcv q).symm
  have haa : ∀ q : κ × Γ, a (e.symm q) = ∫ y, ‖wQ q.1 q.2 y • FQ q.1 y‖ ∂μ := fun q => by
    rw [← integral_smul_eq_self (fun y => ‖wQ q.1 q.2 y • FQ q.1 y‖) (g := α q.1 * φ q.2)]
    exact congrArg (fun f => ∫ x, ‖f x‖ ∂μ) (hcv q).symm
  have hintQ : ∀ q : κ × Γ, Integrable (fun y => wQ q.1 q.2 y • FQ q.1 y) μ := fun q => by
    have hemb := (MeasurableEquiv.smul (α q.1 * φ q.2) : X ≃ᵐ X).measurableEmbedding
    rw [← (measurePreserving_smul (α q.1 * φ q.2) μ).integrable_comp_emb hemb]
    have := (hPpart (e.symm q).2).1 (e.symm q).1
    rw [← hcv q] at this
    exact this
  have hsb : Summable fun q => a (e.symm q) := e.symm.summable_iff.2 hsa
  obtain ⟨hfib, -⟩ := (summable_prod_of_nonneg fun q => ha0 (e.symm q)).1 hsb
  have hsQ : ∀ j, Summable fun γ => ∫ y, ‖wQ j γ y • FQ j y‖ ∂μ := fun j => by
    simpa only [haa] using hfib j
  have hFQsum : ∀ j, (fun y => ∑' γ, wQ j γ y • FQ j y) = FQ j := fun j => by
    funext y
    simpa using ((hwQ1 j y).smul_const (FQ j y)).tsum_eq
  have hQint : ∀ j, Integrable (FQ j) μ := fun j => by
    have h := integrable_tsum_of_summable_norm_integral μ (fun γ y => wQ j γ y • FQ j y)
      (fun γ => hintQ (j, γ)) (hsQ j)
    rwa [hFQsum j] at h
  refine ⟨hQint, ?_⟩
  have hQpart := fun j => hasSum_integral_smul_of_partition μ (wQ j) (hwQm j) (hwQ0 j)
    (hwQ1 j) (FQ j) (hQint j)
  have hstb : Summable fun q => t (e.symm q) := e.symm.summable_iff.2 hst
  calc ∑ i, ∫ x, (ρ x : ℂ) * P i x ∂μ = ∑ i, ∑' γ, t (γ, i) :=
        Finset.sum_congr rfl fun i _ => ((hPpart i).2.tsum_eq).symm
    _ = ∑' γ, ∑ i, t (γ, i) := (Summable.tsum_finsetSum fun i _ => (hPpart i).2.summable).symm
    _ = ∑' γ, ∑' i, t (γ, i) := by simp only [tsum_fintype]
    _ = ∑' p, t p := hst.tsum_prod.symm
    _ = ∑' q, t (e.symm q) := (e.symm.tsum_eq t).symm
    _ = ∑' j, ∑' γ, t (e.symm (j, γ)) := hstb.tsum_prod
    _ = ∑ j, ∑' γ, ∫ y, wQ j γ y • FQ j y ∂μ := by
        rw [tsum_fintype]; simp only [hta]
    _ = ∑ j, ∫ x, (ρ x : ℂ) * Q j ((α j)⁻¹ • x) ∂μ :=
        Finset.sum_congr rfl fun j _ => (hQpart j).2.tsum_eq

end GlobalTheory.EisM
