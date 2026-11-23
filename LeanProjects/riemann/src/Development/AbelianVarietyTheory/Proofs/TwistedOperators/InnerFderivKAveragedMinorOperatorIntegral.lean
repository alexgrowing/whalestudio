import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.SphJet.PsDer

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private lemma aestronglyMeasurable_of_continuous_compact {K E : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [OpensMeasurableSpace K] [NormedAddCommGroup E] (μ : Measure K) {f : K → E} (hf : Continuous f) :
    AEStronglyMeasurable f μ := by
  have h := hf.continuousOn.aestronglyMeasurable_of_isCompact (μ := μ) isCompact_univ MeasurableSet.univ
  rwa [Measure.restrict_univ] at h

private lemma integrable_of_continuous_compact' {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] [NormedAddCommGroup E] (μ : Measure K) [IsFiniteMeasure μ]
    {f : K → E} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (aestronglyMeasurable_of_continuous_compact μ hf) C
    (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

theorem hasDerivAt_integral_cpt {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] {F F' : ℂ → K → ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 (0 : ℂ))
    (hF : ∀ t ∈ s, Continuous (F t)) (hF' : ContinuousOn (fun x : ℂ × K => F' x.1 x.2) (s ×ˢ Set.univ))
    (hd : ∀ k, ∀ t ∈ s, HasDerivAt (F · k) (F' t k) t) :
    HasDerivAt (fun t => ∫ k, F t k ∂μ) (∫ k, F' 0 k ∂μ) 0 := by
  have h0 : (0 : ℂ) ∈ s := mem_of_mem_nhds hs
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hs
  have hcpt : IsCompact (Metric.closedBall (0 : ℂ) r ×ˢ (Set.univ : Set K)) :=
    (isCompact_closedBall 0 r).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hrs subset_rfl))
  have hF'0 : Continuous (F' 0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun k => ⟨h0, Set.mem_univ k⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.closedBall_mem_nhds 0 hr) ?_ (integrable_of_continuous_compact' μ (hF 0 h0))
    (aestronglyMeasurable_of_continuous_compact μ hF'0) ?_ (integrable_const C) ?_).2
  · exact Filter.eventually_of_mem hs fun t ht => aestronglyMeasurable_of_continuous_compact μ (hF t ht)
  · exact Filter.Eventually.of_forall fun k t ht => hC (t, k) ⟨ht, Set.mem_univ k⟩
  · exact Filter.Eventually.of_forall fun k t ht => hd k t (hrs ht)

private lemma analyticAt_leadMinor' (z₀ : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) :
    AnalyticAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => leadMinor z l hl) z₀ := by
  have he : ∀ a b : Fin n, AnalyticAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) z₀ := fun a b =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).analyticAt z₀
  simp only [leadMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine AnalyticAt.mul ?_ ?_
  · exact analyticAt_const
  · exact Finset.analyticAt_fun_prod _ fun i _ => he _ _

theorem analyticOnNhd_Phi (lam : Fin n → ℝ) : AnalyticOnNhd ℂ (Phi lam) (Omega n) := by
  intro z hz
  have hz' : ∀ i : Fin n, leadMinor z (i.val + 1) i.isLt ≠ 0 := hz
  show AnalyticAt ℂ (fun y => ∏ i : Fin n, leadMinor y (i.val + 1) i.isLt ^ (-(sInt lam i))) z
  exact Finset.analyticAt_fun_prod _ fun i _ => (analyticAt_leadMinor' z _ _).fun_zpow (hz' i)

theorem continuous_conj {ε : Fin n → Bool} {X : Type} [TopologicalSpace X] {f : X → KG ε}
    {g : X → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p => (toMK (f p))⁻¹ * g p * toMK (f p)) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = toMK k⁻¹ := fun k => by
    simp [toMK, toM, Matrix.coe_units_inv]
  have e : (fun p => (toMK (f p))⁻¹ * g p * toMK (f p)) = fun p => toMK (f p)⁻¹ * g p * toMK (f p) := by
    funext p; rw [hinv]
  rw [e]
  exact ((hK.comp hf.inv).matrix_mul hg).matrix_mul (hK.comp hf)

private lemma toMK_inv_mul_mul_toMK_mem_Omega {ε : Fin n → Bool} {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U1 ε)
    (k : KG ε) : (toMK k)⁻¹ * z * toMK k ∈ Omega n :=
  hz _ ((mem_KG ε _).1 k.2)

private lemma continuous_toMK_inv_mul_mul_toMK {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun k : KG ε => (toMK k)⁻¹ * M * toMK k) :=
  continuous_conj (f := fun k => k) (g := fun _ => M) continuous_id continuous_const

private lemma continuous_inner_tau_toMK {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    (u v : W) : Continuous (fun k : KG ε => ⟪u, τ (toMK k) v⟫_ℂ) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hd := h.2.2.1 u v
  exact hd.continuousOn.comp_continuous hK fun k =>
    ⟨((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).isUnit, ((mem_KG ε _).1 k.2).2⟩

private lemma continuous_tau_toMK_apply {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    (v : W) : Continuous (fun k : KG ε => τ (toMK k) v) := by
  haveI : FiniteDimensional ℂ W := h.1
  let b := stdOrthonormalBasis ℂ W
  have e : (fun k : KG ε => τ (toMK k) v) = fun k => ∑ i, ⟪b i, τ (toMK k) v⟫_ℂ • b i := by
    funext k; exact (b.sum_repr' _).symm
  rw [e]
  exact continuous_finset_sum _ fun i _ => (continuous_inner_tau_toMK h (b i) v).smul continuous_const

private lemma continuous_Phi_conj_toMK {ε : Fin n → Bool} (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ U1 ε) : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k)) :=
  continuous_iff_continuousAt.2 fun k =>
    ContinuousAt.comp (g := Phi lam) (f := fun k : KG ε => (toMK k)⁻¹ * z * toMK k)
      (analyticOnNhd_Phi lam _ (toMK_inv_mul_mul_toMK_mem_Omega hz k)).continuousAt (continuous_toMK_inv_mul_mul_toMK z).continuousAt

theorem inner_ps_eq {ε : Fin n → Bool} (lam : Fin n → ℝ) {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U1 ε) (y u : W) :
    ⟪y, ps ε lam τ w z u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * z * toMK k) *
      (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  haveI : FiniteDimensional ℂ W := h.1
  have hv : Continuous (fun k : KG ε => τ (toMK k) w) := continuous_tau_toMK_apply h w
  have hR : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have h1 := ((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp
      ((innerSL ℂ).continuous.comp hv)).clm_apply hv
    simpa using h1
  have hG : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    (continuous_Phi_conj_toMK lam hz).smul hR
  have hGi := integrable_of_continuous_compact' (muK ε) hG
  have hGu := hGi.apply_continuousLinearMap u
  simp only [ps]
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply hGi u,
    ← integral_inner hGu y]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_right]
  ring

theorem inner_fderiv_ps : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ z ∈ U1 ε, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (y x : W), Integrable (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) (muK ε) ∧ ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε) := by
  intro n ε lam W _ _ τ w hHC hTau z hz A y x
  haveI : FiniteDimensional ℂ W := hTau.1
  obtain ⟨hopen, -, hdiff, -⟩ := psBasic n ε lam W τ w hHC hTau
  have hU : IsOpen (U1 ε) := hopen
  have hSn : {t : ℂ | z + t • A ∈ U1 ε} ∈ 𝓝 (0 : ℂ) := by
    have hcont : Continuous (fun t : ℂ => z + t • A) := continuous_const.add (continuous_id.smul continuous_const)
    exact hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))
  have hpsD : DifferentiableAt ℂ (ps ε lam τ w) z := hdiff.differentiableAt (hopen.mem_nhds hz)
  have hline : HasDerivAt (fun t : ℂ => z + t • A) A 0 := by
    have h := ((hasDerivAt_id' (0 : ℂ)).smul_const A).const_add z
    rw [one_smul] at h
    exact h
  have hg1 : HasDerivAt (fun t : ℂ => ⟪y, ps ε lam τ w (z + t • A) x⟫_ℂ)
      ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ 0 := by
    let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
    have h1 := hpsD.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    have h3 := h2
    simp only [L, Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply] at h3
    exact h3
  have hv : Continuous (fun k : KG ε => τ (toMK k) w) := continuous_tau_toMK_apply hTau w
  have hc : Continuous (fun k : KG ε => ⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) :=
    (continuous_const.inner hv).mul (hv.inner continuous_const)
  have hconj : Continuous (fun p : ℂ × KG ε => (toMK p.2)⁻¹ * (z + p.1 • A) * toMK p.2) :=
    continuous_conj continuous_snd (continuous_const.add (continuous_fst.smul continuous_const))
  have hmem : ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, ∀ k : KG ε,
      (toMK k)⁻¹ * (z + t • A) * toMK k ∈ Omega n := fun t ht k => toMK_inv_mul_mul_toMK_mem_Omega ht k
  have hAn := analyticOnNhd_Phi (n := n) lam
  have hdA := hAn.fderiv
  have hFc : ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, Continuous (fun k : KG ε =>
      Phi lam ((toMK k)⁻¹ * (z + t • A) * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) :=
    fun t ht => (continuous_Phi_conj_toMK lam ht).mul hc
  have hF'c : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (Phi lam) ((toMK p.2)⁻¹ * (z + p.1 • A) * toMK p.2)
      ((toMK p.2)⁻¹ * A * toMK p.2) * (⟪y, τ (toMK p.2) w⟫_ℂ * ⟪τ (toMK p.2) w, x⟫_ℂ))
      ({t : ℂ | z + t • A ∈ U1 ε} ×ˢ Set.univ) := by
    intro p hp
    have h1 : ContinuousAt (fun q : ℂ × KG ε =>
        fderiv ℂ (Phi lam) ((toMK q.2)⁻¹ * (z + q.1 • A) * toMK q.2)) p :=
      ContinuousAt.comp (g := fderiv ℂ (Phi lam))
        (f := fun q : ℂ × KG ε => (toMK q.2)⁻¹ * (z + q.1 • A) * toMK q.2)
        (hdA _ (hmem p.1 hp.1 p.2)).continuousAt hconj.continuousAt
    have h2 : Continuous (fun q : ℂ × KG ε => (toMK q.2)⁻¹ * A * toMK q.2) :=
      continuous_conj continuous_snd continuous_const
    exact ((h1.clm_apply h2.continuousAt).mul (hc.comp continuous_snd).continuousAt).continuousWithinAt
  have hder : ∀ k : KG ε, ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, HasDerivAt
      (fun s : ℂ => Phi lam ((toMK k)⁻¹ * (z + s • A) * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ))
      (fderiv ℂ (Phi lam) ((toMK k)⁻¹ * (z + t • A) * toMK k) ((toMK k)⁻¹ * A * toMK k) *
        (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) t := by
    intro k t ht
    have hl : HasDerivAt (fun s : ℂ => (toMK k)⁻¹ * (z + s • A) * toMK k) ((toMK k)⁻¹ * A * toMK k) t := by
      have e : (fun s : ℂ => (toMK k)⁻¹ * (z + s • A) * toMK k) =
          fun s => (toMK k)⁻¹ * z * toMK k + s • ((toMK k)⁻¹ * A * toMK k) := by
        funext s; simp [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      have h := ((hasDerivAt_id' t).smul_const ((toMK k)⁻¹ * A * toMK k)).const_add ((toMK k)⁻¹ * z * toMK k)
      rw [one_smul] at h
      exact h
    exact ((hAn _ (hmem t ht k)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hl).mul_const _
  have hD := hasDerivAt_integral_cpt (muK ε) hSn hFc hF'c hder
  have hg2 : HasDerivAt (fun t : ℂ => ⟪y, ps ε lam τ w (z + t • A) x⟫_ℂ)
      ((Module.finrank ℂ W : ℂ) * ∫ k, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * (z + (0 : ℂ) • A) * toMK k)
        ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε)) 0 := by
    refine (hD.const_mul _).congr_of_eventuallyEq ?_
    filter_upwards [hSn] with t ht
    exact inner_ps_eq lam hTau ht y x
  have heq := hg1.unique hg2
  simp only [zero_smul, add_zero] at heq
  refine ⟨?_, heq⟩
  have hcont0 : Continuous (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k)
      ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) := by
    refine continuous_iff_continuousAt.2 fun k => ContinuousAt.mul ?_ hc.continuousAt
    exact (ContinuousAt.comp (g := fderiv ℂ (Phi lam)) (f := fun k : KG ε => (toMK k)⁻¹ * z * toMK k)
      (hdA _ (toMK_inv_mul_mul_toMK_mem_Omega hz k)).continuousAt
      (continuous_toMK_inv_mul_mul_toMK z).continuousAt).clm_apply (continuous_toMK_inv_mul_mul_toMK A).continuousAt
  exact integrable_of_continuous_compact' (muK ε) hcont0

end GlobalTheory.SphJet.PsDer
