import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSum

namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma mean_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ENNReal) (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (s : Set α) (F : α → ℂ) :
    (((c • μ) s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂(c • μ) = ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩
  have hc' : ((c.toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [Measure.restrict_smul, integral_smul_measure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, Complex.ofReal_mul, mul_inv, Complex.real_smul]
  calc _ = ((μ s).toReal : ℂ)⁻¹ * (∫ y in s, F y ∂μ) *
        (((c.toReal : ℝ) : ℂ)⁻¹ * ((c.toReal : ℝ) : ℂ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc', mul_one]

lemma mean_haar {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (s : Set G) (F : G → ℂ) :
    ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ = ((ν s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂ν := by
  haveI : ProperSpace G := FiniteDimensional.proper_real G
  have h := Measure.isAddLeftInvariant_eq_smul ν μ
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  rw [h, ENNReal.smul_def]
  exact (mean_smul μ _ (ENNReal.coe_ne_zero.mpr hpos.ne') ENNReal.coe_ne_top s F).symm

variable (X : Data E r) (la : Wt X.Ψ r)

noncomputable def fjI (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℝ) : ℂ :=
  P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)

lemma flow_differentiable (ξ : Fin r → E) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun s : X.Ψ → ℂ => X.flow ξ s x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  intro s
  simp only [Data.flow, Matrix.mul_apply, Data.flowMat, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact (differentiable_apply τ) s

lemma fjI_continuous (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous (fjI X ξ ν P x) := by
  have hflow0 : X.flow ξ (fun _ => (0 : ℂ)) x = x := by
    funext τ
    change X.flowMat ξ τ 0 * mat x τ = x τ
    rw [flowMat_eq]
    simp only [mul_zero, neg_zero, zero_smul, add_zero, one_mul]
    rfl
  have hmaps : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s
    have h0 := (flow_mem_dom_iff (X := X) hξ x hx (fun _ => (0 : ℂ))).mp (by rw [hflow0]; exact hx)
    rw [flow_mem_dom_iff (X := X) hξ x hx]
    simpa using h0
  have hc1 : Continuous (fun s : X.Ψ → ℝ => X.flow ξ (fun τ => (s τ : ℂ)) x) :=
    (flow_differentiable X ξ x).continuous.comp
      (continuous_pi fun τ => Complex.continuous_ofReal.comp (continuous_apply τ))
  have hc2 : Continuous (fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x)) :=
    hP.1.continuousOn.comp_continuous hc1 hmaps
  unfold fjI
  exact hc2.mul (by fun_prop)

lemma fjI_periodic (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξΛ : ξ ∈ X.Λ)
    (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ)
    (hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (p : X.Ψ → ℝ) (hp : p ∈ X.periods la) (s : X.Ψ → ℝ) :
    fjI X ξ ν P x (p + s) = fjI X ξ ν P x s := by
  have hflow0 : X.flow ξ (fun _ => (0 : ℂ)) x = x := by
    funext τ
    change X.flowMat ξ τ 0 * mat x τ = x τ
    rw [flowMat_eq]
    simp only [mul_zero, neg_zero, zero_smul, add_zero, one_mul]
    rfl
  have hmaps : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s
    have h0 := (flow_mem_dom_iff (X := X) hξ x hx (fun _ => (0 : ℂ))).mp (by rw [hflow0]; exact hx)
    rw [flow_mem_dom_iff (X := X) hξ x hx]
    simpa using h0
  have hadd : X.flow ξ (fun τ => (((p + s) τ : ℝ) : ℂ)) x =
      X.flow ξ (cR X p) (X.flow ξ (fun τ => (s τ : ℂ)) x) := by
    funext τ
    change X.flowMat ξ τ _ * mat x τ = X.flowMat ξ τ _ * mat (X.flow ξ _ x) τ
    rw [mat_flow, ← mul_assoc, flowMat_mul (X := X) hξ]
    congr 2
    simp [cR]
  unfold fjI
  rw [hadd, sec_periodic (X := X) la P hP hξΛ hξ hp _ (hmaps s)]
  congr 1
  obtain ⟨k, hk⟩ := hν p hp
  have hsplit : ∑ τ, (ν τ : ℂ) * (((p + s) τ : ℝ) : ℂ) =
      ∑ τ, (ν τ : ℂ) * (p τ : ℂ) + ∑ τ, (ν τ : ℂ) * (s τ : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.add_apply]
    push_cast
    ring
  rw [hsplit, mul_add, Complex.exp_add]
  have hk' : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (p τ : ℂ)) = 1 := by
    have h1 : ∑ τ, (ν τ : ℂ) * (p τ : ℂ) = (k : ℂ) / 2 := by
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) hk
      push_cast at h2
      linear_combination h2 / 2
    rw [h1, show -(4 * (Real.pi : ℂ) * I) * ((k : ℂ) / 2) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [hk', one_mul]

lemma exists_basis : ∃ ω : Module.Basis (Fin (Fintype.card X.Ψ)) ℝ (X.Ψ → ℝ),
    Submodule.span ℤ (Set.range ω) = perL X la := by
  classical
  let b := Module.Free.chooseBasis ℤ (perL X la)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (perL X la)) = Fintype.card X.Ψ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, perL_rank]
  refine ⟨(b.ofZLatticeBasis ℝ (perL X la)).reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem fj_eq_fourCoeff (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {n : ℕ} (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ))
    (hω : Submodule.span ℤ (Set.range ω) = perL X la) (ν : X.Ψ → ℝ) (k : Fin n → ℤ)
    (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) :
    X.fj la ξ ν P x = ReciprocityTheory.L2DbarEstimates.Y.fourCoeff
      (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)) 0 k := by
  classical

  have hper : X.periods la = (Submodule.span ℤ (Set.range ω)).toAddSubgroup := by
    rw [hω]
    rfl
  have hcond : ∀ p ∈ X.periods la, ∃ k' : ℤ, 2 * ∑ τ, ν τ * p τ = k' := by
    intro p hp
    rw [hper] at hp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
    refine ⟨∑ j, c j * k j, ?_⟩
    have hc : ∀ τ, (∑ j, c j • ω j) τ = ∑ j, (c j : ℝ) * ω j τ := fun τ => by
      simp [Finset.sum_apply, zsmul_eq_mul]
    simp only [hc]
    push_cast
    simp only [← hk, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hF0 : IsAddFundamentalDomain (X.periods la) (ZSpan.fundamentalDomain ω) volume := by
    rw [hper]
    exact ZSpan.isAddFundamentalDomain ω volume
  have hex : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ :=
    ⟨_, ZSpan.fundamentalDomain_measurableSet ω, hF0,
      pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero ω),
      (ZSpan.fundamentalDomain_isBounded ω).measure_lt_top⟩
  have hcount : ((X.periods la : Set (X.Ψ → ℝ))).Countable :=
    (Set.countable_range (fun c : Fin n → ℤ => ∑ j, c j • ω j)).mono fun p hp => by
      rw [hper] at hp
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
  haveI : Countable (X.periods la) := hcount.to_subtype
  unfold Data.fj
  rw [if_pos hcond, dif_pos hex]
  obtain ⟨-, hD, -, -⟩ := hex.choose_spec
  show ((volume hex.choose).toReal : ℂ)⁻¹ * ∫ s in hex.choose, fjI X ξ ν P x s = _

  rw [hD.measure_eq hF0, hD.setIntegral_eq hF0 (f := fjI X ξ ν P x)
    (fun g s => fjI_periodic X la P hP hξ.1 hξ.2.1 ν hcond hx g g.2 s)]

  set T := ω.equivFunL.symm with hTdef
  haveI : (Measure.map T volume).IsAddHaarMeasure := T.isAddHaarMeasure_map volume
  rw [mean_haar volume (Measure.map T volume) (ZSpan.fundamentalDomain ω) (fjI X ξ ν P x)]
  have hmp : MeasurePreserving T volume (Measure.map T volume) :=
    T.continuous.measurable.measurePreserving volume
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  rw [← hmp.setIntegral_preimage_emb hemb _ (ZSpan.fundamentalDomain ω),
    Measure.map_apply T.continuous.measurable (ZSpan.fundamentalDomain_measurableSet ω)]
  have hpre : T ⁻¹' ZSpan.fundamentalDomain ω = Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
    ext t
    have hTt : T t = ω.equivFun.symm t := rfl
    have hrep : ∀ i, ω.repr (ω.equivFun.symm t) i = t i := fun i => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [Set.mem_preimage, ZSpan.mem_fundamentalDomain, Set.mem_univ_pi, hTt]
    simp only [hrep]
  have hvol : volume (Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) = 1 := by
    rw [Real.volume_pi_Ico]
    simp
  have hae : (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) =ᵐ[volume]
      (Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1) := by
    rw [MeasureTheory.volume_pi]
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm
  rw [hpre, hvol, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_mul,
    setIntegral_congr_set hae]
  unfold ReciprocityTheory.L2DbarEstimates.Y.fourCoeff
  congr 1
  funext t
  have hT : ∀ τ, (T t) τ = ∑ j, t j * ω j τ := fun τ => by
    rw [show T t = ω.equivFun.symm t from rfl, Module.Basis.equivFun_symm_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hk' : ∀ j, (k j : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * (ω j τ : ℂ) := fun j => by
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) (hk j)
    push_cast at h2
    exact h2.symm
  unfold fjI
  simp only [hT, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, hk']
  push_cast
  congr 1
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
