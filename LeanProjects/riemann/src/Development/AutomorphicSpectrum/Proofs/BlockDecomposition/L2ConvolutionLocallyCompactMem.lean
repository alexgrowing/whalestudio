import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AutomorphicL2Convolution

private theorem descend_eq_sec_lemma {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (q : Quot Γ) : descend Γ φ q = φ (sec Γ q) := by
  have h2 : mk Γ (Quotient.out q) = mk Γ (sec Γ q) := (Quotient.out_eq q).trans (mk_sec q).symm
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  show φ (Quotient.out q) = φ (sec Γ q)
  rw [← hγ, hφ _ γ.2]

private theorem descend_rmul_lemma_2 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (g : G) (q : Quot Γ) :
    descend Γ φ (rmul Γ g q) = φ (sec Γ q * g) := by
  rw [descend_eq_sec_lemma hφ]
  have h1 : rmul Γ g q = mk Γ (sec Γ q * g) := by
    rw [← rmul_mk, mk_sec]
  have h2 : mk Γ (sec Γ (rmul Γ g q)) = mk Γ (sec Γ q * g) := (mk_sec _).trans h1
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  rw [← hγ, hφ _ γ.2]

private theorem coeFn_R_lemma_3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    ∀ᵐ q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ),
      (((R Γ μ) g) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q = φ (sec Γ q * g) := by
  have h2 : (fun q => (h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) (rmul Γ g q)) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => descend Γ φ (rmul Γ g q) :=
    (measurePreserving_rmul g).quasiMeasurePreserving.ae_eq_comp h.coeFn_toL2
  refine (coeFn_R g h.toL2).trans (h2.trans (Filter.Eventually.of_forall fun q => ?_))
  exact descend_rmul_lemma_2 h.1 g q

private theorem integral_norm_sq_lemma_4 {α : Type} [MeasurableSpace α] {m : Measure α} (F : Lp ℂ 2 m) :
    ∫ q, ‖F q‖ ^ 2 ∂m = ‖F‖ ^ 2 := by
  have h1 := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
  simp only [inner_self_eq_norm_sq_to_K] at h1
  simp_rw [← RCLike.ofReal_pow] at h1
  rw [integral_ofReal] at h1
  exact (RCLike.ofReal_inj.mp h1).symm

private theorem setIntegral_norm_le_lemma_5 {α : Type} [MeasurableSpace α] {m : Measure α} {S : Set α}
    (hS : m S < ∞) (F : Lp ℂ 2 m) :
    ∫ q in S, ‖F q‖ ∂m ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
  haveI : IsFiniteMeasure (m.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hsq : Integrable (fun q => ‖F q‖ ^ 2) m := (Lp.memLp F).norm.integrable_sq
  have hint1 : Integrable (fun q => (1 + ‖F q‖ ^ 2) / 2) (m.restrict S) :=
    ((integrable_const (1 : ℝ)).add hsq.restrict).div_const 2
  calc ∫ q in S, ‖F q‖ ∂m ≤ ∫ q in S, (1 + ‖F q‖ ^ 2) / 2 ∂m := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg (F q)) hint1
          (Filter.Eventually.of_forall fun q => ?_)
        nlinarith [sq_nonneg (‖F q‖ - 1)]
    _ = ((∫ q in S, (1 : ℝ) ∂m) + ∫ q in S, ‖F q‖ ^ 2 ∂m) / 2 := by
        rw [integral_div, integral_add (integrable_const (1 : ℝ)) hsq.restrict]
    _ ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
        have := setIntegral_le_integral (s := S) hsq (Filter.Eventually.of_forall fun q => by positivity)
        rw [integral_norm_sq_lemma_4 F] at this
        linarith

theorem memL2_convolution_mem {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L]
    [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G)
    (hj : Continuous j) (D : L → ℂ) (hD : Continuous D) (hDc : HasCompactSupport D) (φ ψ : G → ℂ)
    (_hφ : Continuous φ) (h : MemL2Quotient Γ μ φ) (hψ : ∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) :
    ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  classical
  have hLφ : LeftInv Γ φ := h.1
  have hπ' : GlobalTheory.OpTrace.IsUnitaryRep ((R Γ μ).comp j) :=
    ⟨fun y w => norm_R (j y) w, fun w => (continuous_R w).comp hj⟩
  have hDint : Integrable D ν := hD.integrable_of_hasCompactSupport hDc
  obtain ⟨hTint, hTv⟩ := isRepOp_of_integrable (μ := ν) hπ' hDint h.toL2
  set T := GlobalTheory.OpTrace.repOp ((R Γ μ).comp j) ν D with hTdef
  have hLψ : LeftInv Γ ψ := by
    intro γ hγ g
    rw [hψ (γ * g), hψ g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (γ * g * j y) * D y = φ (g * j y) * D y
    rw [mul_assoc γ g (j y), hLφ γ hγ]
  have hmeasH : Measurable fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1 :=
    (_hφ.measurable.comp ((measurableEmbedding_sec.measurable.comp measurable_snd).mul
      (hj.measurable.comp measurable_fst))).mul (hD.measurable.comp measurable_fst)
  have hprod : ∀ S : Set (Quot Γ), MeasurableSet S → GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S < ∞ →
      Integrable (fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1)
        (ν.prod ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)) := by
    intro S hS hSf
    haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
    rw [integrable_prod_iff hmeasH.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · have hc := coeFn_R_lemma_3 h (j y)
      refine ((((Lp.memLp (((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable
        one_le_two).mul_const (D y)).congr ?_
      exact ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq])
    · refine Integrable.mono'
        (hDint.norm.mul_const (((∫ q in S, (1 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) +
          ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ ^ 2) / 2))
        (hmeasH.norm.aestronglyMeasurable.integral_prod_right') (Filter.Eventually.of_forall fun y => ?_)
      have hc := coeFn_R_lemma_3 h (j y)
      rw [Real.norm_of_nonneg (integral_nonneg fun q => norm_nonneg _)]
      have e1 : ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)
          = (∫ q in S, ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) * ‖D y‖ := by
        simp_rw [norm_mul]
        rw [integral_mul_const]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq]))
      have hb := setIntegral_norm_le_lemma_5 hSf ((((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))
      have hn : ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖
          = ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ := norm_R _ _
      rw [hn] at hb
      show ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) ≤ _
      rw [e1, mul_comm _ (‖D y‖)]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hkey : (fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => ψ (sec Γ q) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · intro S hS hSf
      haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
      exact ((Lp.memLp (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable one_le_two
    · intro S hS hSf
      exact (hprod S hS hSf).integral_prod_right.congr
        (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
    · intro S hS hSf
      have hSf' : GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S ≠ ∞ := hSf.ne
      have hstep : ∀ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
          (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ
          = ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
        intro y
        have hc := coeFn_R_lemma_3 h (j y)
        rw [inner_smul_right, L2.inner_indicatorConstLp_one, integral_mul_const, mul_comm (D y)]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by
          simp only [MonoidHom.comp_apply]; exact hq))
      calc ∫ q in S, (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)
          = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ), (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ :=
            (L2.inner_indicatorConstLp_one hS hSf' _).symm
        _ = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              ((∫ y, D y • ((R Γ μ).comp j) y h.toL2 ∂ν : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ := by
            rw [hTv]; rfl
        _ = ∫ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ ∂ν :=
            (integral_inner hTint _).symm
        _ = ∫ y, ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∂ν :=
            integral_congr_ae (Filter.Eventually.of_forall hstep)
        _ = ∫ q in S, ∫ y, φ (sec Γ q * j y) * D y ∂ν ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_integral_swap (hprod S hS hSf)
        _ = ∫ q in S, ψ (sec Γ q) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_congr_ae (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
  have hae : descend Γ ψ =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q :=
    Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun q => descend_eq_sec_lemma hLψ q) hkey.symm
  have hmem : MemL2Quotient Γ μ ψ := ⟨hLψ, MemLp.ae_eq hae.symm (Lp.memLp _)⟩
  refine ⟨hmem, fun W hW hvW => ?_⟩
  have hEq : hmem.toL2 = T h.toL2 := Lp.ext (hmem.coeFn_toL2.trans hae)
  rw [hEq]
  exact IsSubrep.map_mem_of_isRepOp (π := (R Γ μ).comp j) ⟨hW.1, fun y w hw => hW.2 (j y) w hw⟩
    (isRepOp_of_integrable hπ' hDint) hvW

end GlobalTheory.CompanionTheory.AutomorphicL2Convolution
