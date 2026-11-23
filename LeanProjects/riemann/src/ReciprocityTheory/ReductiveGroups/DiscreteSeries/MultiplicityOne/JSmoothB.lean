import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmoothA

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SmoothA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

section linf
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem expDer_op (Y : Mat k r) (t : ℝ) :
    Filter.Tendsto (slope (fun u : ℝ => NormedSpace.exp (u • Y)) t) (nhdsWithin t {t}ᶜ)
      (nhds (Y * NormedSpace.exp (t • Y))) := by
  exact hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_exp_smul_const' Y t)

end linf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev ninf : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem ninf_succ_le : ninf + 1 ≤ ninf := by
  show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]

theorem ninf_ne_zero : ninf ≠ 0 := by
  simp [ninf]

section dx

def mulL (X : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

theorem mulL_apply (X x : Mat k r) : mulL X x = X * x := rfl

def mulLL : Mat k r →L[ℝ] (Mat k r →L[ℝ] Mat k r) :=
  LinearMap.toContinuousLinearMap
    { toFun := mulL
      map_add' := fun a b => by ext1 x; simp [mulL_apply, Matrix.add_mul]
      map_smul' := fun c a => by
        ext1 x; simp [mulL_apply] }

theorem mulLL_apply (X x : Mat k r) : mulLL X x = X * x := rfl

def DX (X : Mat k r) (Φ : Mat k r → ℂ) : Mat k r → ℂ := fun x => fderiv ℝ Φ x (-(X * x))

def Dw (l : List (Mat k r)) (Φ : Mat k r → ℂ) : Mat k r → ℂ := l.foldr DX Φ

theorem DX_contDiff {Φ : Mat k r → ℂ} (hΦ : ContDiff ℝ ninf Φ) (X : Mat k r) : ContDiff ℝ ninf (DX X Φ) := by
  exact (hΦ.fderiv_right ninf_succ_le).clm_apply (mulL X).contDiff.neg

theorem DX_tsupport (Φ : Mat k r → ℂ) (X : Mat k r) : tsupport (DX X Φ) ⊆ tsupport Φ := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  apply tsupport_fderiv_subset ℝ (f := Φ)
  apply subset_tsupport
  intro h
  apply hx
  simp [DX, h]

theorem Dw_contDiff {Φ : Mat k r → ℂ} (hΦ : ContDiff ℝ ninf Φ) : ∀ l : List (Mat k r), ContDiff ℝ ninf (Dw l Φ)
  | [] => hΦ
  | X :: l => DX_contDiff (Dw_contDiff hΦ l) X

theorem Dw_tsupport (Φ : Mat k r → ℂ) : ∀ l : List (Mat k r), tsupport (Dw l Φ) ⊆ tsupport Φ
  | [] => subset_rfl
  | X :: l => (DX_tsupport _ X).trans (Dw_tsupport Φ l)

theorem Dw_joint {Φ : Mat k r → ℂ} (hΦ : ContDiff ℝ ninf Φ) :
    ∀ j : ℕ, ContDiff ℝ ninf (fun p : (Fin j → Mat k r) × Mat k r => Dw (List.ofFn p.1) Φ p.2)
  | 0 => by
    simp only [List.ofFn_zero]
    exact hΦ.comp contDiff_snd
  | j + 1 => by
    have IH := Dw_joint hΦ j
    have e : (fun p : (Fin (j + 1) → Mat k r) × Mat k r => Dw (List.ofFn p.1) Φ p.2) =
        fun p => fderiv ℝ (fun y => Dw (List.ofFn (fun i => p.1 i.succ)) Φ y) p.2 (-(mulLL (p.1 0) p.2)) := by
      funext p
      simp only [List.ofFn_succ, Dw, List.foldr_cons, DX, mulLL_apply]
    rw [e]
    have hT : ContDiff ℝ ninf (fun q : (Fin (j + 1) → Mat k r) => fun i : Fin j => q i.succ) :=
      contDiff_pi.2 fun i => contDiff_apply ℝ (Mat k r) i.succ
    have hf : ContDiff ℝ ninf (Function.uncurry
        (fun (p : (Fin (j + 1) → Mat k r) × Mat k r) (y : Mat k r) => Dw (List.ofFn (fun i => p.1 i.succ)) Φ y)) :=
      IH.comp ((hT.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd)
    refine (hf.fderiv contDiff_snd ninf_succ_le).clm_apply ?_
    exact ((mulLL.contDiff.comp ((contDiff_apply ℝ (Mat k r) (0 : Fin (j + 1))).comp contDiff_fst)).clm_apply contDiff_snd).neg

theorem Dw_bound {Φ : Mat k r → ℂ} (hΦ : ContDiff ℝ ninf Φ) (hc : HasCompactSupport Φ) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Fin j → Mat k r, (∀ i a b, ‖q i a b‖ ≤ 1) → ∀ x, ‖Dw (List.ofFn q) Φ x‖ ≤ M := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Fin j → Mat k r) 1).prod hc).exists_bound_of_continuousOn
    (Dw_joint hΦ j).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun q hq x => ?_⟩
  by_cases hx : x ∈ tsupport Φ
  · have hq' : q ∈ Metric.closedBall (0 : Fin j → Mat k r) 1 := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      exact (Matrix.norm_le_iff zero_le_one).2 (hq i)
    exact (hC (q, x) ⟨hq', hx⟩).trans (le_max_left _ _)
  · have : Dw (List.ofFn q) Φ x = 0 := by
      by_contra hne
      exact hx (Dw_tsupport Φ _ (subset_tsupport _ hne))
    rw [this, norm_zero]
    exact le_max_right _ _

end dx

section pint

variable {μ : Measure (Mt k r)} {h : Mt k r → ℝ} {Mh : ℝ} {U K : Set (Mt k r)}

def pd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : Mt k r × Mt k r → E) :
    Mt k r × Mt k r → (Mt k r →L[ℝ] E) :=
  fun p => (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inl ℝ (Mt k r) (Mt k r))

theorem pd_hasFDerivAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : Mt k r × Mt k r → E}
    (hΨ : ContDiff ℝ ninf Ψ) (g y : Mt k r) :
    HasFDerivAt (fun g' => Ψ (g', y)) (pd Ψ (g, y)) g := by
  exact ((hΨ.differentiable ninf_ne_zero) (g, y)).hasFDerivAt.comp g (hasFDerivAt_prodMk_left g y)

theorem pd_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : Mt k r × Mt k r → E}
    (hΨ : ContDiff ℝ ninf Ψ) : ContDiff ℝ ninf (pd Ψ) := by
  exact (hΨ.fderiv_right ninf_succ_le).clm_comp contDiff_const

theorem pd_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : Mt k r × Mt k r → E}
    (hΨ : ContDiff ℝ ninf Ψ) (hU : IsOpen U)
    (hz : ∀ g ∈ U, ∀ y : Mt k r, (Matrix.of y : Mat k r) ∈ GV k r → y ∉ K → Ψ (g, y) = 0) :
    ∀ g ∈ U, ∀ y : Mt k r, (Matrix.of y : Mat k r) ∈ GV k r → y ∉ K → pd Ψ (g, y) = 0 := by
  intro g hg y hy hyK
  have h0 : HasFDerivAt (fun g' => Ψ (g', y)) (0 : Mt k r →L[ℝ] E) g :=
    (hasFDerivAt_const (0 : E) g).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hg) fun g' hg' => hz g' hg' y hy hyK)
  exact (pd_hasFDerivAt hΨ g y).unique h0

private theorem intg_lemma (hμK : ∀ S : Set (Mt k r), IsCompact S → μ S < ∞) (hG : μ (GV k r)ᶜ = 0)
    (hh : AEStronglyMeasurable h μ) (hMh : ∀ᵐ y ∂μ, |h y| ≤ Mh) (hK : IsCompact K)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Θ : Mt k r → E} (hΘ : Continuous Θ)
    (hz : ∀ y : Mt k r, (Matrix.of y : Mat k r) ∈ GV k r → y ∉ K → Θ y = 0) :
    Integrable (fun y => h y • Θ y) μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ.continuousOn
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hint : Integrable (K.indicator fun _ => Mh * max C 0) μ :=
    (integrableOn_const (hμK K hK).ne enorm_ne_top).integrable_indicator hKm
  have hGae : ∀ᵐ y ∂μ, y ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 hG
  refine hint.mono' (hh.smul hΘ.aestronglyMeasurable) ?_
  filter_upwards [hMh, hGae] with y hy1 hyG
  by_cases hyK : y ∈ K
  · rw [Set.indicator_of_mem hyK, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hy1 ((hC y hyK).trans (le_max_left _ _)) (norm_nonneg _) ((abs_nonneg _).trans hy1)
  · simp [Set.indicator, hyK, hz y hyG hyK]

theorem pint_hasFDerivAt (hμK : ∀ S : Set (Mt k r), IsCompact S → μ S < ∞) (hG : μ (GV k r)ᶜ = 0)
    (hh : AEStronglyMeasurable h μ) (hMh : ∀ᵐ y ∂μ, |h y| ≤ Mh) (hU : IsOpen U) (hK : IsCompact K)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : Mt k r × Mt k r → E}
    (hΨ : ContDiff ℝ ninf Ψ)
    (hz : ∀ g ∈ U, ∀ y : Mt k r, (Matrix.of y : Mat k r) ∈ GV k r → y ∉ K → Ψ (g, y) = 0)
    {g₀ : Mt k r} (hg₀ : g₀ ∈ U) :
    HasFDerivAt (fun g => ∫ y, h y • Ψ (g, y) ∂μ) (∫ y, h y • pd Ψ (g₀, y) ∂μ) g₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU g₀ hg₀
  have hcb : IsCompact (Metric.closedBall g₀ (ε / 2) ×ˢ K) := (isCompact_closedBall _ _).prod hK
  obtain ⟨C, hC⟩ := hcb.exists_bound_of_continuousOn (pd_contDiff hΨ).continuous.continuousOn
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hGae : ∀ᵐ y ∂μ, y ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 hG
  have hΨc : ∀ g, Continuous fun y => Ψ (g, y) := fun g =>
    hΨ.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  have hpc : ∀ g, Continuous fun y => pd Ψ (g, y) := fun g =>
    (pd_contDiff hΨ).continuous.comp (Continuous.prodMk continuous_const continuous_id)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun g y => h y • Ψ (g, y))
    (F' := fun g y => h y • pd Ψ (g, y)) (bound := K.indicator fun _ => Mh * max C 0)
    (Metric.ball_mem_nhds g₀ (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun g => hh.smul (hΨc g).aestronglyMeasurable
  · exact intg_lemma hμK hG hh hMh hK (hΨc g₀) fun y hy hyK => hz g₀ hg₀ y hy hyK
  · exact hh.smul (hpc g₀).aestronglyMeasurable
  · filter_upwards [hMh, hGae] with y hy1 hyG g hg
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hy1 ((hC (g, y) ⟨Metric.ball_subset_closedBall hg, hyK⟩).trans (le_max_left _ _))
        (norm_nonneg _) ((abs_nonneg _).trans hy1)
    · have : pd Ψ (g, y) = 0 :=
        pd_zero hΨ hU hz g (hεU (Metric.ball_subset_ball (half_le_self hε.le) hg)) y hyG hyK
      simp [this, Set.indicator, hyK]
  · exact (integrableOn_const (hμK K hK).ne enorm_ne_top).integrable_indicator hKm
  · exact Filter.Eventually.of_forall fun y g _ => (pd_hasFDerivAt hΨ g y).const_smul (h y)

theorem pint_contDiffOn (hμK : ∀ S : Set (Mt k r), IsCompact S → μ S < ∞) (hG : μ (GV k r)ᶜ = 0)
    (hh : AEStronglyMeasurable h μ) (hMh : ∀ᵐ y ∂μ, |h y| ≤ Mh) (hU : IsOpen U) (hK : IsCompact K) :
    ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : Mt k r × Mt k r → E),
      ContDiff ℝ ninf Ψ →
      (∀ g ∈ U, ∀ y : Mt k r, (Matrix.of y : Mat k r) ∈ GV k r → y ∉ K → Ψ (g, y) = 0) →
      ContDiffOn ℝ n (fun g => ∫ y, h y • Ψ (g, y) ∂μ) U
  | 0, E, _, _, Ψ, hΨ, hz => by
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun g hg => (pint_hasFDerivAt hμK hG hh hMh hU hK hΨ hz hg).continuousAt.continuousWithinAt
  | n + 1, E, _, _, Ψ, hΨ, hz => by
    have hd := fun g (hg : g ∈ U) => pint_hasFDerivAt hμK hG hh hMh hU hK hΨ hz hg
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
      ⟨fun g hg => (hd g hg).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (pint_contDiffOn hμK hG hh hMh hU hK n (Mt k r →L[ℝ] E) (pd Ψ) (pd_contDiff hΨ)
      (pd_zero hΨ hU hz)).congr fun g hg => (hd g hg).fderiv

end pint

section intg

variable {μ : Measure (Mt k r)} {h : Mt k r → ℝ} {Mh : ℝ} {K : Set (Mt k r)}

theorem pint_integrable (hμK : ∀ S : Set (Mt k r), IsCompact S → μ S < ∞) (hG : μ (GV k r)ᶜ = 0)
    (hh : AEStronglyMeasurable h μ) (hMh : ∀ᵐ y ∂μ, |h y| ≤ Mh) (hK : IsCompact K)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Θ : Mt k r → E} (hΘ : Continuous Θ)
    (hz : ∀ y : Mt k r, (Matrix.of y : Mat k r) ∈ GV k r → y ∉ K → Θ y = 0) :
    Integrable (fun y => h y • Θ y) μ := by
  exact intg_lemma hμK hG hh hMh hK hΘ hz

end intg

section expo

theorem expDer (Y : Mat k r) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Y)) (Y * NormedSpace.exp (t • Y)) t := by
  exact hasDerivAt_iff_tendsto_slope.mpr (expDer_op Y t)

theorem exp_continuous (Y : Mat k r) : Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
  exact continuous_iff_continuousAt.2 fun t => (expDer Y t).continuousAt

def mulR (y : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ y)

theorem curveDer (Y y : Mat k r) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Y) * y) (Y * NormedSpace.exp (t • Y) * y) t := by
  have := (mulR y).hasFDerivAt.comp_hasDerivAt t (expDer Y t)
  exact this

theorem exp_neg_mul (Y : Mat k r) (t : ℝ) (y : Mat k r) :
    NormedSpace.exp ((-t) • Y) * (NormedSpace.exp (t • Y) * y) = y := by
  rw [← Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _
    ((Commute.refl Y).smul_left _ |>.smul_right _), ← add_smul, neg_add_cancel, zero_smul,
    NormedSpace.exp_zero, Matrix.one_mul]

end expo

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

section rep

variable {X : SigData k r}

theorem sig_mul {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) (v : X.Hs) :
    X.σ (a * b) v = X.σ a (X.σ b v) := by
  rw [X.rep.1.2 a ha b hb]
  rfl

theorem sig_one (v : X.Hs) : X.σ 1 v = v := by
  rw [X.rep.1.1]
  rfl

theorem sig_norm {g : Mat k r} (hg : g ∈ GV k r) (v : X.Hs) : ‖X.σ g v‖ = ‖v‖ := by
  exact X.rep.2.1 g hg v

theorem sig_inner {g : Mat k r} (hg : g ∈ GV k r) (u v : X.Hs) : ⟪X.σ g u, X.σ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let L : X.Hs →ₗᵢ[ℂ] X.Hs := ⟨(X.σ g).toLinearMap, fun v => X.rep.2.1 g hg v⟩
  exact L.inner_map_map u v

theorem sig_adj {g : Mat k r} (hg : g ∈ GV k r) (u v : X.Hs) : ⟪u, X.σ g v⟫_ℂ = ⟪X.σ g⁻¹ u, v⟫_ℂ := by
  have h1 : X.σ g (X.σ g⁻¹ u) = u := by
    rw [← sig_mul hg (gv_inv_mem hg), gv_mul_inv hg, sig_one]
  calc ⟪u, X.σ g v⟫_ℂ = ⟪X.σ g (X.σ g⁻¹ u), X.σ g v⟫_ℂ := by rw [h1]
    _ = ⟪X.σ g⁻¹ u, v⟫_ℂ := sig_inner hg _ _

end rep

section vec

variable (D : RealPlaceData k r Wp Wq) (X : SigData k r)

def V (Φ : Mat k r → ℂ) : X.Hs := sigInt D X Φ X.w

variable {D X}

private theorem vint_lemma {Ψ : Mat k r → ℂ} (hc : Continuous Ψ) (hs : HasCompactSupport Ψ) {a : Mat k r}
    (ha : a ∈ GV k r) :
    Integrable (fun x : Mt k r => Ψ (Matrix.of x) • X.σ (a * Matrix.of x) X.w) D.μG := by
  haveI : IsFiniteMeasureOnCompacts D.μG := ⟨D.haarG.finite_compact⟩
  have hGae : ∀ᵐ x ∂D.μG, x ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 D.haarG.conc
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hc' : Continuous fun x : Mt k r => Ψ (Matrix.of x) := hc.comp hof
  have hs' : HasCompactSupport fun x : Mt k r => Ψ (Matrix.of x) := hs
  have hΨi : Integrable (fun x : Mt k r => Ψ (Matrix.of x)) D.μG := hc'.integrable_of_hasCompactSupport hs'
  have hcon : ContinuousOn (fun x : Mt k r => X.σ (a * Matrix.of x) X.w) (GV k r) :=
    (X.rep.2.2 X.w).comp (continuous_const.matrix_mul hof).continuousOn fun x hx => gv_mul ha hx
  have hσm : AEStronglyMeasurable (fun x : Mt k r => X.σ (a * Matrix.of x) X.w) D.μG := by
    have := hcon.aestronglyMeasurable (μ := D.μG) gv_meas
    convert this using 1
    exact (Measure.restrict_eq_self_of_ae_mem hGae).symm
  refine hΨi.norm.mono' (hΨi.aestronglyMeasurable.smul hσm) ?_
  filter_upwards [hGae] with x hx
  rw [norm_smul, show ‖X.σ (a * Matrix.of x) X.w‖ = 1 from (sig_norm (gv_mul ha hx) X.w).trans X.w_norm, mul_one]

theorem V_int {Φ : Mat k r → ℂ} (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    Integrable (fun x : Mt k r => Φ (Matrix.of x) • X.σ (Matrix.of x) X.w) D.μG := by
  have := vint_lemma (D := D) (X := X) hc hs gv_one
  simpa only [Matrix.one_mul] using this

theorem V_apply {Φ : Mat k r → ℂ} (hc : Continuous Φ) (hs : HasCompactSupport Φ) {g : Mat k r}
    (hg : g ∈ GV k r) :
    X.σ g (V D X Φ) = ∫ x : Mt k r, Φ (Matrix.of x) • X.σ (g * Matrix.of x) X.w ∂D.μG := by
  have hi := V_int (D := D) (X := X) hc hs
  simp only [V, sigInt]
  rw [← ContinuousLinearMap.integral_comp_comm _ hi]
  refine integral_congr_ae ?_
  filter_upwards [mem_ae_iff.2 D.haarG.conc] with x hx
  simp only [map_smul]
  rw [show X.σ (g * Matrix.of x) X.w = X.σ g (X.σ (Matrix.of x) X.w) from sig_mul hg hx X.w]

theorem V_transl {Φ : Mat k r → ℂ} (hc : Continuous Φ) (hs : HasCompactSupport Φ) {e : Mat k r}
    (he : e ∈ GV k r) : X.σ e (V D X Φ) = V D X (fun x => Φ (e⁻¹ * x)) := by
  rw [V_apply hc hs he]
  have hGae : ∀ᵐ x ∂D.μG, x ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 D.haarG.conc
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hσm : AEStronglyMeasurable (fun x : Mt k r => X.σ (Matrix.of x) X.w) D.μG := by
    have := ContinuousOn.aestronglyMeasurable (μ := D.μG)
      (f := fun x : Mt k r => X.σ (Matrix.of x) X.w) (X.rep.2.2 X.w) gv_meas
    convert this using 1
    exact (Measure.restrict_eq_self_of_ae_mem hGae).symm
  have hlc : Continuous (lmulM (k := k) (r := r) e) := continuous_const.matrix_mul hof
  have hmeas : Measurable (lmulM (k := k) (r := r) e) := hlc.measurable
  have hF : AEStronglyMeasurable (fun y : Mt k r => Φ (e⁻¹ * Matrix.of y) • X.σ (Matrix.of y) X.w) D.μG :=
    (hc.comp (continuous_const.matrix_mul hof)).aestronglyMeasurable.smul hσm
  have key := integral_map (μ := D.μG) hmeas.aemeasurable
    (f := fun y : Mt k r => Φ (e⁻¹ * Matrix.of y) • X.σ (Matrix.of y) X.w)
    (by rw [D.haarG.left e he]; exact hF)
  rw [D.haarG.left e he] at key
  simp only [V, sigInt]
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Φ (Matrix.of x) • X.σ (e * Matrix.of x) X.w = Φ (e⁻¹ * (e * Matrix.of x)) • X.σ (e * Matrix.of x) X.w
  rw [← Matrix.mul_assoc, gv_inv_mul he, Matrix.one_mul]

theorem V_hasDerivAt {Φ : Mat k r → ℂ} (hΦ : ContDiff ℝ ninf Φ) (hs : HasCompactSupport Φ) (Y : Mat k r) :
    HasDerivAt (fun t : ℝ => V D X (fun x => Φ (NormedSpace.exp (t • Y) * x)))
      (V D X (fun x => fderiv ℝ Φ x (Y * x))) 0 := by
  haveI : IsFiniteMeasureOnCompacts D.μG := ⟨D.haarG.finite_compact⟩
  have hGae : ∀ᵐ x ∂D.μG, x ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 D.haarG.conc
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hσm : AEStronglyMeasurable (fun x : Mt k r => X.σ (Matrix.of x) X.w) D.μG := by
    have := ContinuousOn.aestronglyMeasurable (μ := D.μG)
      (f := fun x : Mt k r => X.σ (Matrix.of x) X.w) (X.rep.2.2 X.w) gv_meas
    convert this using 1
    exact (Measure.restrict_eq_self_of_ae_mem hGae).symm
  have hexp := exp_continuous Y
  have hE : Continuous fun p : ℝ × Mat k r => NormedSpace.exp (p.1 • Y) * p.2 :=
    (hexp.comp continuous_fst).matrix_mul continuous_snd
  have hfd : Continuous (fderiv ℝ Φ) := (hΦ.fderiv_right ninf_succ_le).continuous
  have hG : Continuous fun p : ℝ × Mat k r =>
      fderiv ℝ Φ (NormedSpace.exp (p.1 • Y) * p.2) (Y * NormedSpace.exp (p.1 • Y) * p.2) :=
    (hfd.comp hE).clm_apply ((continuous_const.matrix_mul (hexp.comp continuous_fst)).matrix_mul continuous_snd)
  have hSc : IsCompact ((fun p : ℝ × Mat k r => NormedSpace.exp ((-p.1) • Y) * p.2) ''
      (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport Φ)) := ((isCompact_closedBall _ _).prod hs).image
    ((hexp.comp continuous_fst.neg).matrix_mul continuous_snd)
  set S : Set (Mt k r) := (fun p : ℝ × Mat k r => NormedSpace.exp ((-p.1) • Y) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport Φ) with hSdef
  have hS : IsCompact S := hSc
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hSc).exists_bound_of_continuousOn hG.continuousOn
  have hSm : MeasurableSet (α := Mt k r) S := hS.isClosed.measurableSet
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := D.μG)
    (F := fun t (x : Mt k r) => Φ (NormedSpace.exp (t • Y) * Matrix.of x) • X.σ (Matrix.of x) X.w)
    (F' := fun t (x : Mt k r) => fderiv ℝ Φ (NormedSpace.exp (t • Y) * Matrix.of x)
      (Y * NormedSpace.exp (t • Y) * Matrix.of x) • X.σ (Matrix.of x) X.w)
    (x₀ := (0 : ℝ)) (bound := fun x : Mt k r => S.indicator (fun _ => max C 0) x)
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul] at key
    exact key.2
  · exact Filter.Eventually.of_forall fun t =>
      (hΦ.continuous.comp (hE.comp (continuous_const.prodMk hof))).aestronglyMeasurable.smul hσm
  · have := V_int (D := D) (X := X) hΦ.continuous hs
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] using this
  · exact (hG.comp (continuous_const.prodMk hof)).aestronglyMeasurable.smul hσm
  · filter_upwards [hGae] with x hx t ht
    rw [norm_smul, show ‖X.σ (Matrix.of x) X.w‖ = 1 from (sig_norm hx X.w).trans X.w_norm, mul_one]
    show _ ≤ S.indicator (fun _ => max C 0) x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      exact (hC (t, Matrix.of x) ⟨Metric.ball_subset_closedBall ht, hxS⟩).trans (le_max_left _ _)
    · have h0 : fderiv ℝ Φ (NormedSpace.exp (t • Y) * Matrix.of x) = 0 := by
        by_contra hne
        apply hxS
        exact ⟨(t, NormedSpace.exp (t • Y) * Matrix.of x),
          ⟨Metric.ball_subset_closedBall ht, tsupport_fderiv_subset ℝ (subset_tsupport _ hne)⟩,
          exp_neg_mul Y t _⟩
      rw [h0, ContinuousLinearMap.zero_apply, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  · exact (integrableOn_const (D.haarG.finite_compact S hS).ne enorm_ne_top).integrable_indicator hSm
  · refine Filter.Eventually.of_forall fun x t _ => ?_
    have h1 := ((hΦ.differentiable ninf_ne_zero) (NormedSpace.exp (t • Y) * Matrix.of x)).hasFDerivAt.comp_hasDerivAt t
      (curveDer Y (Matrix.of x) t)
    exact h1.smul_const (X.σ (Matrix.of x) X.w)

theorem V_intH {Ψ : Mat k r → ℂ} (hc : Continuous Ψ) (hs : HasCompactSupport Ψ) {h : Mat k r}
    (hh : h ∈ GV k r) :
    Integrable (fun x : Mt k r => Ψ (Matrix.of x) • X.σ (h * Matrix.of x) X.w) D.μG := by
  exact vint_lemma hc hs hh

end vec

end ReciprocityTheory.ChartRestriction.DS.Mult1.SmoothA
