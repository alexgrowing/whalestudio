import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLeNormDev
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsUpqSubmatrix
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaFrameOfDelta
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFSublevelLtTop

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.OrbitInterpolation

theorem exists_of_approx {α ι : Type} [Finite ι] (S : Submodule ℂ (α → ℂ)) (a : α) (p : ι → α)
    (h : ∀ η : ℝ, 0 < η → ∃ u ∈ S, ‖u a - 1‖ ≤ η ∧ ∀ i, ‖u (p i)‖ ≤ η) :
    ∃ u ∈ S, u a = 1 ∧ ∀ i, u (p i) = 0 := by
  haveI := Fintype.ofFinite ι
  set L : (α → ℂ) →ₗ[ℂ] ℂ × (ι → ℂ) :=
    (LinearMap.proj a).prod (LinearMap.pi fun i => LinearMap.proj (p i)) with hL
  have hc : IsClosed ((S.map L : Submodule ℂ (ℂ × (ι → ℂ))) : Set (ℂ × (ι → ℂ))) :=
    Submodule.closed_of_finiteDimensional _
  have hm : ((1, 0) : ℂ × (ι → ℂ)) ∈ ((S.map L : Submodule ℂ (ℂ × (ι → ℂ))) : Set (ℂ × (ι → ℂ))) := by
    rw [← hc.closure_eq, Metric.mem_closure_iff]
    intro η hη
    obtain ⟨u, hu, h1, h2⟩ := h (η / 2) (half_pos hη)
    refine ⟨L u, Submodule.mem_map_of_mem hu, lt_of_le_of_lt ?_ (half_lt_self hη)⟩
    rw [dist_comm, dist_eq_norm, Prod.norm_def]
    refine max_le (by simpa [hL] using h1) ?_
    refine (pi_norm_le_iff_of_nonneg (half_pos hη).le).2 fun i => ?_
    simpa [hL] using h2 i
  obtain ⟨u, hu, he⟩ := hm
  refine ⟨u, hu, ?_, fun i => ?_⟩
  · simpa [hL] using congrArg Prod.fst he
  · simpa [hL] using congrFun (congrArg Prod.snd he) i

theorem sum_range_blocks (p : ℕ) (M : ℕ → ℝ) (a a' : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (if i < p then a else a') * (M (i + 1) - M i) =
      a * (M (min n p) - M 0) + a' * (M (max n p) - M p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n < p
    · rw [if_pos h, min_eq_left h.le, max_eq_right h.le, min_eq_left (Nat.succ_le_of_lt h),
        max_eq_right (Nat.succ_le_of_lt h)]
      ring
    · have h' := not_lt.1 h
      rw [if_neg h, min_eq_right h', max_eq_left h', min_eq_right (h'.trans (Nat.le_succ n)),
        max_eq_left (h'.trans (Nat.le_succ n))]
      ring

theorem sum_fin_blocks {r p : ℕ} (hp : p ≤ r) (L : Fin (r + 1) → ℝ) (a a' : ℝ) :
    ∑ i : Fin r, (if (i : ℕ) < p then a else a') * (L i.succ - L i.castSucc) =
      a * (L ⟨p, Nat.lt_succ_of_le hp⟩ - L 0) + a' * (L (Fin.last r) - L ⟨p, Nat.lt_succ_of_le hp⟩) := by
  set M : ℕ → ℝ := fun n => if h : n < r + 1 then L ⟨n, h⟩ else 0 with hM
  have e : ∀ k : Fin (r + 1), L k = M k := fun k => by simp only [hM, dif_pos k.isLt]
  simp only [e, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last]
  rw [Fin.sum_univ_eq_sum_range (fun i => (if i < p then a else a') * (M (i + 1) - M i)),
    sum_range_blocks, min_eq_right hp, max_eq_left hp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exp_neg_phla_le {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) {la : Wt X.Ψ r}
    (hla : BlockConst X la) (t : ℝ) :
    ∃ K : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ t → Real.exp (-phla X la (cpt X x0 z)) ≤ K := by
  obtain ⟨a, a', rfl⟩ := blockConst_iff.1 hla
  refine ⟨Real.exp (∑ τ, |(a' τ : ℝ) - a τ| * t), fun z hz ht => Real.exp_le_exp.2 ?_⟩
  have hz' : cpt X x0 z ∈ X.dom := hz
  have hd : ∀ τ i, 0 < ‖dmin X.Gm (cpt X x0 z) τ i‖ := fun τ i =>
    norm_pos_iff.2 (IW.dmin_ne_zero X hz' τ i)
  have hq : ∀ τ (i : Fin r),
      0 < ‖dmin X.Gm (cpt X x0 z) τ i.succ / dmin X.Gm (cpt X x0 z) τ i.castSucc‖ := fun τ i => by
    rw [norm_div]; exact div_pos (hd _ _) (hd _ _)
  unfold phla Data.nfac
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hq τ k) _).ne'),
    neg_mul, neg_neg, Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Real.log_prod (fun k _ => (Real.rpow_pos_of_pos (hq τ k) _).ne'), Finset.mul_sum]
  have e : ∀ i : Fin r, 2 * Real.log (‖dmin X.Gm (cpt X x0 z) τ i.succ /
      dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^
        (-((if (i : ℕ) < X.p0 then a τ else a' τ : ℤ) : ℝ) / 2)) =
      (if (i : ℕ) < X.p0 then -(a τ : ℝ) else -(a' τ : ℝ)) *
        (Real.log ‖dmin X.Gm (cpt X x0 z) τ i.succ‖ - Real.log ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖) := by
    intro i
    rw [Real.log_rpow (hq τ i), norm_div, Real.log_div (hd _ _).ne' (hd _ _).ne']
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => e i,
    sum_fin_blocks X.p0_le (fun k => Real.log ‖dmin X.Gm (cpt X x0 z) τ k‖)]
  have z0 : dmin X.Gm (cpt X x0 z) τ 0 = 1 := by simp [dmin, lminor]
  have hl : ∀ M : Matrix (Fin r) (Fin r) ℂ, lminor M (Fin.last r) = M.det := fun M => rfl
  have z1 : ‖dmin X.Gm (cpt X x0 z) τ (Fin.last r)‖ = 1 := by
    have n0 := FramePotential.norm_dmin_of_isOrth X h0 τ (Fin.last r)
    have n1 := FramePotential.lminor_cpt X h0 z τ (Fin.last r)
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
    unfold dmin at n0 ⊢
    rw [hl] at n0 n1 ⊢
    rw [← Matrix.mul_nonsing_inv_cancel_left _ (mat (cpt X x0 z) τ) hu, FrameDegreeData.gram_mul, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, norm_mul, norm_mul, n0,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.norm_conj, n1]
    simp
  have h1 := neg_log_factor_le_rhX h0 hz' τ
  have h2 := (FramePotential.factor_mem X h0 hz' τ).2
  rw [FramePotential.lminor_cpt X h0, norm_one, one_pow, div_one] at h1 h2
  rw [rhX_cpt h0 hz] at h1
  have h3 := Real.log_nonpos (norm_nonneg _) h2
  rw [z0, z1, norm_one, Real.log_one]
  generalize Real.log ‖dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ = l at h1 h3 ⊢
  have h4 : -l ≤ t := h1.trans ht
  calc _ = -((a' τ : ℝ) - a τ) * (-l) := by ring
    _ ≤ |(a' τ : ℝ) - a τ| * (-l) := mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)

theorem ae_mem_OmF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (OntoB.isOpen_OmF X x0).measurableSet)

theorem lintegral_lt_top (hMI : MeasInvStatement (E := E)) {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
    (h0 : IsOrth X x0) {la : Wt X.Ψ r} (hla : BlockConst X la) {bb ε : ℝ} (hbb : 0 ≤ bb)
    {χ : ℝ → ℝ} (hχ0 : ∀ u, ε ≤ u → χ u = 0) (hχ1 : ∀ u, |χ u| ≤ 1) {ψ : Frame X.Ψ r → ℝ}
    (hψ : ∀ x ∈ X.dom, ψ x ≤ 0) {F : V (nd X) → ℂ}
    (hfin : ∫⁻ z, ENNReal.ofReal (‖(χ (rhF X x0 z) : ℂ) - F z‖ ^ 2 *
        Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) ∂muF X x0 < ⊤) :
    ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) / kaF X x0 bb z)
      ∂muF X x0 < ⊤ := by
  obtain ⟨K, hK⟩ := exp_neg_phla_le h0 hla ε
  set S : Set (Frame X.Ψ r) := {y | rhX X x0 y ≤ ε} with hS
  have hSm : MeasurableSet (cpt X x0 ⁻¹' S) :=
    (OntoB.cd_cpt X x0).continuous.measurable (measurableSet_le (measurable_rhX h0) measurable_const)
  have hSμ : muF X x0 (cpt X x0 ⁻¹' S) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono_ae ?_) (SublevelFin.muF_sublevel_lt_top hMI r X x0 h0 ε)
    filter_upwards [ae_mem_OmF X x0] with z hz h
    have h' : rhX X x0 (cpt X x0 z) ≤ ε := h
    rw [rhX_cpt h0 hz] at h'
    exact h'
  have hae : ∀ᵐ z ∂muF X x0,
      ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) / kaF X x0 bb z) ≤
      (cpt X x0 ⁻¹' S).indicator (fun _ => ENNReal.ofReal (2 * (K * Real.exp (bb * ε)))) z +
        ENNReal.ofReal 2 * ENNReal.ofReal (‖(χ (rhF X x0 z) : ℂ) - F z‖ ^ 2 *
          Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) := by
    filter_upwards [ae_mem_OmF X x0] with z hz
    have hk : 0 < kaF X x0 bb z := Real.exp_pos _
    set w := Real.exp (-phla X la (cpt X x0 z)) / kaF X x0 bb z with hw
    set w' := Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z with hw'
    have hw0 : 0 < w := div_pos (Real.exp_pos _) hk
    have hww : w ≤ w' := div_le_div_of_nonneg_right
      (Real.exp_le_exp.2 (by linarith [hψ _ hz])) hk.le
    set c : ℂ := (χ (rhF X x0 z) : ℂ) with hc
    have h1 : ENNReal.ofReal (2 * (‖c‖ ^ 2 * w)) ≤
        (cpt X x0 ⁻¹' S).indicator (fun _ => ENNReal.ofReal (2 * (K * Real.exp (bb * ε)))) z := by
      by_cases hzS : rhF X x0 z ≤ ε
      · have hm : z ∈ cpt X x0 ⁻¹' S := by
          show rhX X x0 (cpt X x0 z) ≤ ε
          rwa [rhX_cpt h0 hz]
        rw [Set.indicator_of_mem hm]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ two_pos.le)
        have c1 : ‖c‖ ^ 2 ≤ 1 := by
          rw [hc, Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_one₀ (abs_nonneg _) (hχ1 _)
        refine (mul_le_of_le_one_left hw0.le c1).trans ?_
        rw [hw, div_eq_mul_inv, kaF, ← Real.exp_neg]
        refine mul_le_mul (hK z hz hzS) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
          ((Real.exp_pos _).le.trans (hK z hz hzS))
        nlinarith [mul_le_mul_of_nonneg_left hzS hbb]
      · simp [hc, hχ0 _ (not_le.1 hzS).le]
    have h3 : ‖F z‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 + 2 * ‖c - F z‖ ^ 2 := by
      have : ‖F z‖ ≤ ‖c‖ + ‖c - F z‖ := by simpa using norm_sub_le c (c - F z)
      nlinarith [norm_nonneg (F z), norm_nonneg c, norm_nonneg (c - F z), sq_nonneg (‖c‖ - ‖c - F z‖)]
    rw [← ENNReal.ofReal_mul two_pos.le, mul_div_assoc, mul_div_assoc, ← hw, ← hw']
    refine le_trans ?_ (add_le_add_left h1 _)
    have hw1 : 0 < w' := hw0.trans_le hww
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add (by positivity) (by positivity)).le
    nlinarith [mul_le_mul_of_nonneg_right h3 hw0.le,
      mul_le_mul_of_nonneg_left hww (sq_nonneg ‖c - F z‖)]
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_add_left (measurable_const.indicator hSm), lintegral_indicator_const hSm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSμ,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

theorem exists_ball {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {ε : ℝ} (hε : 0 < ε) {κ : Frame X.Ψ r → ℝ}
    (hκ : ∀ x ∈ X.dom, 0 < κ x)
    (hloc : ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) :
    ∃ ρ A : ℝ, 0 < ρ ∧ 0 < A ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → z ∈ OmF X x ∧
      rhF X x z ≤ ε ∧ 1 ≤ A * κ x * (Real.exp (-phla X la (cpt X x z)) / κ (cpt X x z)) := by
  obtain ⟨ρ₂, Cκ, hρ₂, hκn⟩ := hloc
  obtain ⟨ρ₁, c, C₁, hρ₁, hc, hON⟩ := OrthNear.orthNear r X la
  have h0 := OrthNear.isOrth_x0F X
  have hz0 := IW.zero_mem_OmF X _ h0
  have hcont : ContinuousAt (rhF X (x0F X)) 0 := (OntoB.rhF_contDiffAt hz0).continuousAt
  have hr0 : rhF X (x0F X) 0 < ε := by rwa [← rhX_cpt h0 hz0, IW.cpt_zero, rhX_self h0]
  obtain ⟨ρ₃, hρ₃, hb⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hr0))
  refine ⟨min ρ₁ (min ρ₂ ρ₃), (|Cκ| + 1) / c ^ 2, lt_min hρ₁ (lt_min hρ₂ hρ₃), by positivity,
    fun x hx z hz => ?_⟩
  rw [lt_min_iff, lt_min_iff] at hz
  obtain ⟨hd, -, -, hn, -⟩ := hON x hx z hz.1
  refine ⟨hd, ?_, ?_⟩
  · have := hb (y := z) (by rw [dist_zero_right]; exact hz.2.2)
    unfold rhF at this ⊢
    simp only [OrthNear.dmin_cpt_eq X hx h0]
    exact this.le
  · have hkx := hκ x (IW.orth_mem_dom X x hx)
    have hkz := hκ _ hd
    have h1 : κ (cpt X x z) ≤ (|Cκ| + 1) * κ x :=
      (hκn x hx z hz.2.1).trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cκ]) hkx.le)
    have h2 : c ^ 2 ≤ X.nfac la (cpt X x z) ^ 2 := by gcongr
    rw [KronMetric.exp_neg_phla X la hd]
    calc (1 : ℝ) ≤ ((|Cκ| + 1) * κ x / κ (cpt X x z)) * (X.nfac la (cpt X x z) ^ 2 / c ^ 2) :=
          one_le_mul_of_one_le_of_one_le ((one_le_div hkz).2 h1) ((one_le_div (by positivity)).2 h2)
      _ = _ := by ring

theorem rpow_le_weight {r : ℕ} {X : Data E r} {G : Subgroup (GL (Fin r) E)} {x0 : Frame X.Ψ r}
    (h0 : IsOrth X x0) (hG : ∀ γ ∈ G, IsUStab X.Gm X.Λ γ) {k ε C δ : ℝ} (hδ : 0 < δ)
    {ψ : Frame X.Ψ r → ℝ} (hψ : IsPole X G x0 k ε C δ ψ) {g : GL (Fin r) E} (hg : g ∈ G)
    {z : V (nd X)} (hz : z ∈ OmF X (lact g x0)) (hle : rhF X (lact g x0) z ≤ ε) :
    (rhF X (lact g x0) z + δ) ^ (-(dimX X : ℝ)) ≤ Real.exp C * Real.exp (-ψ (cpt X (lact g x0) z)) := by
  have h1 := isOrth_lact_of_isUStab (hG g hg) h0
  have h2 := hψ.le_log_orbit hG hg hz (by rwa [rhX_cpt h1 hz])
  have h3 := rhX_nonneg h1 hz
  rw [rhX_cpt h1 hz] at h2 h3
  rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

theorem value_le {n : ℕ} {μ : Measure (V n)} {ρ c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) {M : ℝ≥0∞} (hM : M < ⊤)
    {v : ℝ} {f : V n → ℝ} {H : V n → ℝ≥0∞}
    (h : ENNReal.ofReal v ≤ ENNReal.ofReal c * ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal (f z) ∂μ)
    (hf : ∀ z ∈ Metric.ball (0 : V n) ρ, ENNReal.ofReal (f z) ≤ ENNReal.ofReal B * H z)
    (hH : ∫⁻ z, H z ∂μ ≤ M) : v ≤ c * B * M.toReal := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hM.ne, mul_assoc]
  refine h.trans (mul_le_mul_right ?_ _)
  refine (setLIntegral_mono' Metric.isOpen_ball.measurableSet hf).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right ((setLIntegral_le_lintegral _ _).trans hH) _

theorem exists_density (hMI : MeasInvStatement (E := E)) {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
    (h0 : IsOrth X x0) {la : Wt X.Ψ r} {bb ε : ℝ} {χ : ℝ → ℝ} (hχ0 : ∀ u, ε ≤ u → χ u = 0)
    {κ : Frame X.Ψ r → ℝ} (hκm : Measurable κ)
    (hκB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x)
    (hκF : ∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) {ψ : Frame X.Ψ r → ℝ}
    (hW : IsMetricW X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))))
    {F : V (nd X) → ℂ} {P : Frame X.Ψ r → ℂ} (hP : IsBEq X la P)
    (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) {M : ℝ≥0∞}
    (hM : ∫⁻ z, ENNReal.ofReal (‖(χ (rhF X x0 z) : ℂ) - F z‖ ^ 2 *
        Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) ∂muF X x0 ≤ M) :
    ∃ φ : Frame X.Ψ r → ℝ≥0∞, (∀ y ∈ X.dom, ε ≤ rhX X x0 y →
      φ y = ENNReal.ofReal (‖P y‖ ^ 2 * Real.exp (-(phla X la y + ψ y)) / κ y)) ∧
      ∀ x, IsOrth X x → ∫⁻ z, φ (cpt X x z) ∂muF X x ≤ M := by
  set W := X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) with hWd
  set T : Set (Frame X.Ψ r) := {y | ε ≤ rhX X x0 y} with hT
  have hTm : MeasurableSet T := measurableSet_le measurable_const (measurable_rhX h0)
  set φ : Frame X.Ψ r → ℝ≥0∞ :=
    T.indicator fun y => OntoE.phiF X P W y * ENNReal.ofReal (κ y)⁻¹ with hφ
  have hφm : Measurable φ :=
    ((OntoE.phiF_meas X hP.1.continuousOn hW.1).mul hκm.inv.ennreal_ofReal).indicator hTm
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := by
    intro x hx b hb
    have e : rmul x b ∈ T ↔ x ∈ T := by simp only [hT, Set.mem_setOf_eq, rhX_rmul x0 x hb]
    by_cases h : x ∈ T
    · rw [hφ, Set.indicator_of_mem h, Set.indicator_of_mem (e.2 h), OntoE.phiF_B X hP.2 hW x hx b hb,
        hκB x hx b hb]
    · rw [hφ, Set.indicator_of_notMem h, Set.indicator_of_notMem (mt e.1 h)]
  have hv : ∀ y ∈ X.dom, ε ≤ rhX X x0 y →
      φ y = ENNReal.ofReal (‖P y‖ ^ 2 * Real.exp (-(phla X la y + ψ y)) / κ y) := by
    intro y hy h
    rw [hφ, Set.indicator_of_mem (show y ∈ T from h), OntoE.phiF_dom X P W hy, hWd,
      Set.indicator_of_mem hy, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv]
  refine ⟨φ, hv, fun x hx => ?_⟩
  rw [← hMI r X x0 x h0 hx φ hφm hφB]
  refine le_trans (lintegral_mono_ae ?_) hM
  filter_upwards [ae_mem_OmF X x0] with z hz
  by_cases h : ε ≤ rhX X x0 (cpt X x0 z)
  · rw [hv _ hz h, hPF z hz, hκF z hz]
    rw [rhX_cpt h0 hz] at h
    simp [hχ0 _ h]
  · rw [hφ, Set.indicator_of_notMem (show cpt X x0 z ∉ T from h)]
    exact zero_le

theorem exists_approx
    (hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E))
    (hExt : ExtFStatement (E := E)) (hMI : MeasInvStatement (E := E)) (hPE : PoleEx (E := E))
    (hPS : PoleSolve (E := E)) (hPP : PolePoint (E := E)) {r : ℕ} {X : Data E r}
    {G : Subgroup (GL (Fin r) E)} {x0 : Frame X.Ψ r} {la : Wt X.Ψ r} {ρ0 bb m : ℝ}
    (h0 : IsOrth X x0) (hd : 1 ≤ dimX X) (hρ0 : 0 < ρ0) (hG : FreeBall X G x0 ρ0) (hla : BlockConst X la)
    (hbb : 0 ≤ bb) (hm : bb + dimX X / ρ0 < m)
    (hcurv : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ)
    {κ : Frame X.Ψ r → ℝ} (hκm : Measurable κ) (hκ1 : ∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1)
    (hκB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x)
    (hκF : ∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z)
    (hloc : ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x)
    {η : ℝ} (hη : 0 < η) :
    ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧
      InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + 0)))) bb F ∧
      IsBEq X la P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ ‖P x0 - 1‖ ≤ η ∧
      ∀ g ∈ G, g ≠ 1 → ‖P (lact g x0)‖ ≤ η * Real.sqrt (κ (lact g x0)) := by
  have hd' : (0 : ℝ) < dimX X := by exact_mod_cast hd
  have hq : 0 < (dimX X : ℝ) / ρ0 := div_pos hd' hρ0
  obtain ⟨θ, hθ1, hθ⟩ := exists_between ((one_lt_div hq).2 (by linarith : (dimX X : ℝ) / ρ0 < m - bb))
  rw [lt_div_iff₀ hq] at hθ
  obtain ⟨ε, C, hε, hερ, hψ⟩ := hPE r X G x0 ρ0 θ h0 hρ0 hθ1 hG
  obtain ⟨χ, M, -, hχ1, hχ0, hχb, hM, hsol⟩ := hPS r X G x0 la (dimX X * θ / ρ0) ε C bb m h0 hla hε hbb
    (by have : (dimX X : ℝ) * θ / ρ0 = θ * (dimX X / ρ0) := by ring
        linarith) hcurv
  obtain ⟨ρ, A, hρ, hA, hball⟩ := exists_ball X la (half_pos hε) (fun x hx => (hκ1 x hx).1) hloc
  set D : ℝ := Real.exp C * A * M.toReal with hD
  have hD0 : 0 ≤ D := by positivity
  set c : ℝ := η ^ 2 / (D + 1) with hc
  have hc0 : 0 < c := by positivity
  have hcD : c * D ≤ η ^ 2 := by
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg η]
  obtain ⟨δ0, hδ0, hpt⟩ := hPP r X ρ c hd hρ hc0
  have hδ : 0 < min δ0 1 := lt_min hδ0 one_pos
  obtain ⟨ψ, hψ⟩ := hψ (min δ0 1) hδ (min_le_right _ _)
  obtain ⟨F, hF, hFM⟩ := hsol _ ψ hψ
  have hfin := lintegral_lt_top hMI h0 hla hbb hχ0 hχb hψ.2.1 (hFM.trans_lt hM)
  have hka : ∀ z, 0 < kaF X x0 bb z := fun z => Real.exp_pos _
  obtain ⟨P, hP, hPF⟩ := hExt r X x0 h0 la F hF fun K _ _ => by
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt
      (lt_of_le_of_lt (lintegral_mono_ae ?_) hfin)
    filter_upwards [ae_mem_OmF X x0] with z hz
    refine ENNReal.ofReal_le_ofReal (le_div_self (by positivity) (hka z) ?_)
    rw [← hκF z hz]; exact (hκ1 _ hz).2

  have hw : ∀ g ∈ G, ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∀ s : ℝ, 0 ≤ s →
      ENNReal.ofReal (s * (rhF X (lact g x0) z + min δ0 1) ^ (-(dimX X : ℝ))) ≤
      ENNReal.ofReal (Real.exp C * A * κ (lact g x0)) * ENNReal.ofReal (s *
        Real.exp (-(phla X la (cpt X (lact g x0) z) + ψ (cpt X (lact g x0) z))) /
          κ (cpt X (lact g x0) z)) := by
    intro g hg z hz s hs
    have h1 := isOrth_lact_of_isUStab (hG.isUStab hg) h0
    obtain ⟨hzO, hzr, hzw⟩ := hball _ h1 z (mem_ball_zero_iff.1 hz)
    have h2 := rpow_le_weight h0 hG.2.1 hδ hψ hg hzO (by linarith)
    have hk := (hκ1 _ (IW.orth_mem_dom X _ h1)).1
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc _ ≤ s * (Real.exp C * Real.exp (-ψ (cpt X (lact g x0) z))) := mul_le_mul_of_nonneg_left h2 hs
      _ ≤ s * (Real.exp C * Real.exp (-ψ (cpt X (lact g x0) z))) * (A * κ (lact g x0) *
          (Real.exp (-phla X la (cpt X (lact g x0) z)) / κ (cpt X (lact g x0) z))) :=
        le_mul_of_one_le_right (by positivity) hzw
      _ = _ := by rw [neg_add, Real.exp_add]; ring
  refine ⟨F, P, hF, ?_, hP, hPF, ?_, fun g hg hne => ?_⟩
  · unfold InAt
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hfin
    filter_upwards [ae_mem_OmF X x0] with z hz
    have hz' : cpt X x0 z ∈ X.dom := hz
    rw [Set.indicator_of_mem hz', ← ENNReal.ofReal_mul (div_nonneg (by positivity) (hka z).le), add_zero]
    congr 1
    ring
  · have hk := hκ1 _ (IW.orth_mem_dom X _ h0)
    have h1 := hpt x0 h0 _ hδ (min_le_left _ _) (fun z => 1 - F z)
      ((differentiableOn_const _).sub (hF.mono Set.inter_subset_right))
    have h2 := value_le (B := Real.exp C * A * κ x0) hc0.le (by have := hk.1; positivity) hM h1
      (fun z hz => by
        have := hw 1 G.one_mem z hz (‖1 - F z‖ ^ 2) (by positivity)
        obtain ⟨hzO, hzr, -⟩ := hball _ h0 z (mem_ball_zero_iff.1 hz)
        rw [FundSetPf.lact_one, hκF z hzO] at this
        simp only [hχ1 _ hzr, Complex.ofReal_one]
        exact this) hFM
    have h3 : P x0 = F 0 := by
      have := hPF 0 (IW.zero_mem_OmF X x0 h0)
      rwa [IW.cpt_zero] at this
    rw [h3, norm_sub_rev]
    refine abs_le_of_sq_le_sq' ?_ hη.le |>.2
    refine h2.trans (le_trans ?_ hcD)
    calc _ = c * D * κ x0 := by rw [hD]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hk.2
  · have h1 := isOrth_lact_of_isUStab (hG.isUStab hg) h0
    have hk := hκ1 _ (IW.orth_mem_dom X _ h1)
    obtain ⟨-, hW, -⟩ := KronMetric.kronMetric hN r X la ψ (hψ.isInvFn hG.1)
      (fun x hx => (hψ.2.2.1 x hx).1) ⟨0, hψ.2.1⟩
    obtain ⟨φ, hφ, hφM⟩ := exists_density hMI h0 hχ0 hκm hκB hκF hW hP hPF hFM
    have h2 := hpt _ h1 _ hδ (min_le_left _ _) (fun z => P (cpt X (lact g x0) z))
      ((OntoB.hol_comp X _ hP.1).mono Set.inter_subset_right)
    have h3 := value_le (B := Real.exp C * A * κ (lact g x0)) hc0.le (by have := hk.1; positivity) hM h2
      (fun z hz => by
        obtain ⟨hzO, hzr, -⟩ := hball _ h1 z (mem_ball_zero_iff.1 hz)
        have hg' := hG.isUStab (G.inv_mem hg)
        have h4 := hG.2.2 g hg hne _ (MajInv.lact_mem_dom X hg' hzO)
          (by rw [rhX_lact hg', inv_inv, rhX_cpt h1 hzO]; linarith)
        rw [← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one] at h4
        rw [hφ _ hzO (by linarith)]
        exact hw g hg z hz _ (by positivity)) (hφM _ h1)
    rw [IW.cpt_zero] at h3
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt hk.1.le]
    refine h3.trans ?_
    calc _ = c * D * κ (lact g x0) := by rw [hD]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcD hk.1.le

theorem tsum_le_of_le {ι : Type} {f s : ι → ℝ} (hf : Summable f) (hf0 : ∀ i, 0 ≤ f i) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ i, f i ≤ η * s i) {C : ℝ≥0∞} (hC : C < ⊤) (hs : ∑' i, ENNReal.ofReal (s i) ≤ C) :
    ∑' i, f i ≤ η * C.toReal := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_tsum_of_nonneg hf0 hf,
    ENNReal.ofReal_mul hη, ENNReal.ofReal_toReal hC.ne]
  refine le_trans (ENNReal.tsum_le_tsum fun i => ?_)
    (ENNReal.tsum_mul_left.le.trans (mul_le_mul_right hs _))
  rw [← ENNReal.ofReal_mul hη]
  exact ENNReal.ofReal_le_ofReal (h i)

theorem chi_one {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) : X.χ la 1 = 1 := by
  have h := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
  have h0 : X.χ la 1 ≠ 0 := norm_ne_zero_iff.1 (by rw [OntoE.chi_norm X la X.Γ.one_mem]; exact one_ne_zero)
  rw [mul_one] at h
  exact (mul_left_cancel₀ h0 (by rw [← h, mul_one])).symm

theorem orbitInterp :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) →
    PoinStatement (E := E) → ExtFStatement (E := E) → MeasInvStatement (E := E) →
    GlobalTheory.Up.PoleEx (E := E) → GlobalTheory.Up.PoleSolve (E := E) → GlobalTheory.Up.PolePoint (E := E) →
    GlobalTheory.Up.OrbitInterp (E := E) := by
  classical
  intro hN hPoin hExt hMI hPE hPS hPP r X G x0 la ρ0 bb m hPD h0 hd hρ0 hG hla hbb hm hcurv hSS
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  obtain ⟨κ, hκm, hκ1, hκB, hκF, ⟨Cs, hCs, hsum⟩, hloc⟩ :=
    GlobalTheory.kaFrame (E := E) GlobalTheory.FramePotential.frame_potential_basic GlobalTheory.MinorRatioNear.minorRatio_near
      (GlobalTheory.FrameSumBound.frame_sum_bound GlobalTheory.grpSep) r X x0 h0 hPD bb hbb
  obtain ⟨-, hW, hWl⟩ := KronMetric.kronMetric hN r X la (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  obtain ⟨⟨hz, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  let S : Submodule ℂ (Frame X.Ψ r → ℂ) :=
    { carrier := X.SS la
      add_mem' := fun {P Q} hP hQ => hadd P hP Q hQ
      zero_mem' := hz
      smul_mem' := fun a P hP => hsmul a P hP }
  obtain ⟨T, hT⟩ := X.Γ_index
  have hx0 := IW.orth_mem_dom X x0 h0
  obtain ⟨u, hu, hu1, hu0⟩ := exists_of_approx S x0
    (fun s : {s : T // s.1⁻¹ ∈ G ∧ s.1⁻¹ ∉ X.Γ} => lact s.1.1⁻¹ x0) fun η hη => by
    have hη' : 0 < η / (Cs.toReal + 1) := by positivity
    obtain ⟨F, P, hF, hIn, hP, hPF, hP1, hP0⟩ := exists_approx hN hExt hMI hPE hPS hPP h0 hd hρ0 hG hla
      hbb0 hm hcurv hκm hκ1 hκB hκF hloc hη'
    obtain ⟨hs, hbd, -⟩ := hPoin r X x0 h0 hPD la _ bb hW hWl hbb F P hF hIn hP hPF
    have hn : ∀ (γ : X.Γ) (y : Frame X.Ψ r), ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ :=
      fun γ y => by rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have he : η / (Cs.toReal + 1) + η / (Cs.toReal + 1) * Cs.toReal = η := by field_simp; ring
    refine ⟨poin X la P, hSS _ hbd, ?_, fun s => ?_⟩
    · have hs0 := hs x0 hx0
      unfold poin
      rw [hs0.of_norm.tsum_eq_add_tsum_ite 1]
      simp only [OneMemClass.coe_one, chi_one, FundSetPf.lact_one, inv_one, one_mul]
      have hle : ∀ γ : X.Γ, ‖if γ = 1 then 0 else (X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ ≤
          ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ := fun γ => by
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl
      have hs1 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs0
      have h2 := (norm_tsum_le_tsum_norm hs1).trans (tsum_le_of_le hs1 (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          split_ifs with h
          · rw [norm_zero]; positivity
          · rw [hn]
            exact hP0 γ.1 (hG.1 γ.2) fun h' => h (Subtype.ext h')) hCs (hsum x0 hx0))
      rw [add_sub_right_comm, ← he]
      exact (norm_add_le _ _).trans (add_le_add hP1 h2)
    · have hy := MajInv.lact_mem_dom X (hG.isUStab s.2.1) hx0
      have h2 := (norm_tsum_le_tsum_norm (hs _ hy)).trans (tsum_le_of_le (hs _ hy)
        (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          rw [hn, ← FundSetPf.lact_mul]
          refine hP0 _ (G.mul_mem (hG.1 γ.2) s.2.1) fun h => s.2.2 ?_
          rw [eq_inv_of_mul_eq_one_right h]
          exact X.Γ.inv_mem γ.2) hCs (hsum _ hy))
      exact h2.trans (by linarith)
  refine ⟨u, hu, by rw [hu1]; exact one_ne_zero, fun γ hγ hγ' => ?_⟩
  obtain ⟨s, hsT, hs⟩ := hT γ⁻¹ (hG.isUStab (G.inv_mem hγ))
  have e : s⁻¹ = (s⁻¹ * γ⁻¹) * γ := by group
  have e' : γ = (s⁻¹ * γ⁻¹)⁻¹ * s⁻¹ := by group
  have h1 : s⁻¹ ∈ G := by rw [e]; exact G.mul_mem (hG.1 hs) hγ
  have h2 : s⁻¹ ∉ X.Γ := fun h => hγ' (by rw [e']; exact X.Γ.mul_mem (X.Γ.inv_mem hs) h)
  have h3 : u (lact s⁻¹ x0) = 0 := hu0 ⟨⟨s, hsT⟩, h1, h2⟩
  have hu' : u ∈ X.SS la := hu
  rw [e', FundSetPf.lact_mul, hu'.1.1.2.2 _ (X.Γ.inv_mem hs) _
    (MajInv.lact_mem_dom X (hG.isUStab h1) hx0), h3, mul_zero]

end GlobalTheory.Up.OrbitInterpolation
