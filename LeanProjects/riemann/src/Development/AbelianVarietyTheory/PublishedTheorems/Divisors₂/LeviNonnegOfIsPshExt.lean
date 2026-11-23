import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExph
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableOnOfNormLeSumAbsLogAddLogLog

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.Published
open ReciprocityTheory.AnForm.A (IsPsh IsLeviPsh isPsh_iff_isLeviPsh_thm isPsh_sup_thm)
open scoped ContDiff

namespace GlobalTheory.RegularisationModel

section Flat

variable {d : ℕ} {U U' : Set (Fin d → ℂ)} {u u' : (Fin d → ℂ) → ℝ}

theorem isPsh_mono_congr (h : IsPsh U u) (hU : U' ⊆ U) (e : ∀ z ∈ U', u z = u' z) : IsPsh U' u' := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · filter_upwards [(h.1.mono hU) z hz y ((e z hz).trans_lt hy), self_mem_nhdsWithin] with x hx hx'
    rwa [← e x hx']
  · obtain ⟨h₁, h₂⟩ := h.2 z w fun ζ hζ => hU (hd ζ hζ)
    have he : EqOn (fun ζ : ℂ => u (z + ζ • w)) (fun ζ : ℂ => u' (z + ζ • w)) (Metric.sphere 0 |1|) :=
      fun ζ hζ => e _ (hd ζ (by simpa using (mem_sphere_zero_iff_norm.1 hζ).le))
    refine ⟨(circleIntegrable_congr he).1 h₁, ?_⟩
    rw [← Real.circleAverage_congr_sphere he, ← e z (by simpa using hd 0 (by simp))]
    exact h₂

theorem toReal_max (x κ : ℝ) : (max (x : EReal) ((-κ : ℝ) : EReal)).toReal = max x (-κ) := by
  rw [← EReal.coe_strictMono.monotone.map_max, EReal.toReal_coe]

theorem isPshExt_coe (hU : IsOpen U) (h : IsPsh U u) : IsPshExt U fun z => (u z : EReal) := by
  refine ⟨fun z _ => EReal.coe_ne_top _, ?_, fun z hz => subset_closure ⟨hz, EReal.coe_ne_bot _⟩, fun κ => ?_⟩
  · exact continuous_coe_real_ereal.comp_upperSemicontinuousOn h.1 EReal.coe_strictMono.monotone
  · have hc : IsPsh U fun _ => -κ := ⟨upperSemicontinuousOn_const, fun z w _ =>
      ⟨circleIntegrable_const _ _ _, by rw [Real.circleAverage_const]⟩⟩
    refine isPsh_mono_congr (isPsh_sup_thm d Bool U (fun b => if b then u else fun _ => -κ) hU ?_) subset_rfl
      fun z _ => ?_
    · rintro (_ | _)
      · simpa using hc
      · simpa using h
    · rw [toReal_max]
      simp [Finset.sup'_insert]

theorem levi_nonneg_of_isPshExt (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (h : IsPshExt U fun z => (u z : EReal))
    {z : Fin d → ℂ} (hz : z ∈ U) (w : Fin d → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi u z w := by
  have ho : IsOpen (U ∩ u ⁻¹' Ioi (u z - 1)) := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have h₁ : IsPsh (U ∩ u ⁻¹' Ioi (u z - 1)) u := isPsh_mono_congr (h.2.2.2 (1 - u z)) inter_subset_left fun x hx => by
    rw [toReal_max, neg_sub]
    exact max_eq_left (le_of_lt hx.2)
  exact ((isPsh_iff_isLeviPsh_thm d _ u ho (hu.mono inter_subset_left)).1 h₁).2 z ⟨hz, by simp⟩ w

theorem not_isPshExt_bot (hU : U.Nonempty) : ¬ IsPshExt U fun _ => ⊥ := fun h => by
  obtain ⟨z, hz⟩ := hU
  simpa using h.2.2.1 hz

end Flat

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {a θ : ChartForm p σ d} {u : CxPts p σ → ℝ}

theorem isFormPsh_coe_iff (hθ : IsClosedForm R θ) (hu : R.SmoothOn univ u) :
    IsFormPsh R θ (fun y => (u y : EReal)) ↔
      ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, 0 ≤ θ c y ξ + ddcForm u c y ξ := by
  have key (W φ) (hφ : IsPotential R θ W φ) (c : AlgChart p σ d) :
      ContDiffOn ℝ 2 ((fun y => φ y + u y) ∘ c.finChart.symm) (c.finChart.target ∩ c.finChart.symm ⁻¹' W) ∧
      ∀ y ∈ c.e.source, y ∈ W → ∀ ξ, θ c y ξ + ddcForm u c y ξ =
        ReciprocityTheory.AnForm.levi ((fun y => φ y + u y) ∘ c.finChart.symm) (c.finChart y) ξ / Real.pi := by
    have hs : R.SmoothOn W fun y => φ y + u y := fun i => (hφ.2.1 i).add ((hu.mono (subset_univ W)) i)
    refine ⟨((c.contDiffOn_finChart_iff _ W _).2 (hs.chart hφ.1 c)).of_le (WithTop.coe_le_coe.2 le_top), fun y hy hW ξ => ?_⟩
    rw [hφ.2.2 c y hy hW, ← c.leviV_re_eq (hs.contDiffAt_two hφ.1 hy hW), ddcForm, ddcForm, ← add_div,
      ← AlgChart.levi_add (hφ.2.1.contDiffAt_two hφ.1 hy hW) (hu.contDiffAt_two isOpen_univ hy trivial)]
    rfl
  constructor
  · intro h c y hy ξ
    obtain ⟨W, φ, hW, hφ⟩ := hθ y
    rw [(key W φ hφ c).2 y hy hW]
    refine div_nonneg (levi_nonneg_of_isPshExt (c.finChart.isOpen_inter_preimage_symm hφ.1) (key W φ hφ c).1
      (h W φ hφ c) ⟨c.finChart.map_source hy, ?_⟩ ξ) Real.pi_pos.le
    rwa [mem_preimage, c.finChart.left_inv hy]
  · intro h W φ hφ c
    have ho := c.finChart.isOpen_inter_preimage_symm hφ.1
    refine isPshExt_coe ho ((isPsh_iff_isLeviPsh_thm d _ _ ho (key W φ hφ c).1).2 ⟨(key W φ hφ c).1, fun z hz w => ?_⟩)
    have hy := c.finChart.map_target hz.1
    have := h c _ hy w
    rw [(key W φ hφ c).2 _ hy hz.2, c.finChart.right_inv hz.1] at this
    exact (div_nonneg_iff.1 this).elim (·.1) fun h => absurd h.2 Real.pi_pos.not_ge

theorem ddcForm_const (r : ℝ) (c : AlgChart p σ d) (y : CxPts p σ) (ξ : Fin d → ℂ) : ddcForm (fun _ => r) c y ξ = 0 := by
  rw [ddcForm, AlgChart.levi, c.leviV_re_eq (f := fun _ => r) contDiffAt_const]
  simp [ReciprocityTheory.AnForm.levi, Function.comp_def]

theorem kaehler_nonneg (ha : IsKaehlerForm R a) (c : AlgChart p σ d) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (ξ : Fin d → ℂ) : 0 ≤ a c y ξ := by
  rcases eq_or_ne ξ 0 with rfl | h
  · have := (continuous_and_smul ha hy).2 0 0
    simp only [smul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
    exact this.ge
  · exact (ha.2 c y hy ξ h).le

theorem isFormPsh_const (ha : IsKaehlerForm R a) (r : ℝ) : IsFormPsh R a fun _ => (r : EReal) :=
  (isFormPsh_coe_iff (u := fun _ => r) ha.1 fun _ => contDiffOn_const).2 fun c y hy ξ => by
    rw [ddcForm_const, add_zero]
    exact kaehler_nonneg ha c hy ξ

theorem not_isFormPsh_const (hθ : IsClosedForm R θ) (r : ℝ) (c : AlgChart p σ d) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {ξ : Fin d → ℂ} (h : θ c y ξ < 0) : ¬ IsFormPsh R θ fun _ => (r : EReal) := fun h' => by
  have := (isFormPsh_coe_iff (u := fun _ => r) hθ fun _ => contDiffOn_const).1 h' c y hy ξ
  rw [ddcForm_const, add_zero] at this
  exact h.not_ge this

theorem conclusion_const [SmoothOfRelativeDimension d p] (ha : IsKaehlerForm R a) (hθ : IsClosedForm R θ)
    (E : ChartMap p σ d) (r : ℝ) (h : IsFormPsh R θ fun _ => (r : EReal)) :
    IsRegConst a θ (rho a E fun _ => (r : EReal).toReal) 0 0 1 := by
  have e : rho a E (fun _ => (r : EReal).toReal) = fun _ _ => r := funext₂ fun y t => rho_const ha E _ y t
  rw [e]
  refine ⟨le_rfl, le_rfl, one_pos, fun _ => contDiffOn_const, fun _ _ _ _ _ _ => by simp, fun c y hy w _ _ ξ η => ?_⟩
  have := (isFormPsh_coe_iff (u := fun _ => r) hθ fun _ => contDiffOn_const).1 h c y hy ξ.ofLp
  rw [ddcForm_const, add_zero] at this
  have e' : dbar (fun _ : V d × ℂ => (r : ℂ)) = fun _ => 0 := funext fun _ => dbar_const _ _
  rw [leviForm, ddbar, e', del_const]
  simpa using this

end Manifold

open GlobalTheory.ProjVar GlobalTheory.TrueGeo in

theorem hypotheses_inhabited (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) :
    CompactSpace (CxPts Y.str σ) ∧ T2Space (CxPts Y.str σ) ∧
      ∃ (a : ChartForm Y.str σ Y.dim) (E : ChartMap Y.str σ Y.dim), IsKaehlerForm (AnRead.all Y.str σ Y.dim) a ∧
        IsExph a E ∧ IsClosedForm (AnRead.all Y.str σ Y.dim) a ∧
        IsFormPsh (AnRead.all Y.str σ Y.dim) a fun _ => ((0 : ℝ) : EReal) := by
  have ha := isKaehlerForm_curvForm (ProjPos.fubiniStudy_weight_pullback_isSmooth Y.ι Y.ι_str (AnRead.all Y.str σ Y.dim))
    (ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos _ _ _)
  obtain ⟨E, hE⟩ := exists_isExph F Y σ _ ha
  exact ⟨CxPts.compactSpace σ Y.isProjOver, CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver, _, E, ha, hE, ha.1,
    isFormPsh_const ha 0⟩

section Mono

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {a θ : ChartForm p σ d} {Ψ : CxPts p σ → ℝ → ℝ} {A K δ A' K' δ' : ℝ}

theorem isRegConst_mono (ha : IsKaehlerForm R a) (h : IsRegConst a θ Ψ A K δ) (hA : A ≤ A') (hK : K ≤ K') (hδ' : 0 < δ')
    (hδ : δ' ≤ δ) : IsRegConst a θ Ψ A' K' δ' := by
  refine ⟨h.A_nonneg.trans hA, h.K_nonneg.trans hK, hδ', fun c => (h.smooth c).mono
    (prod_mono subset_rfl fun w hw => ⟨hw.1, hw.2.trans_le hδ⟩), fun y s hs t ht hst => ?_, fun c y hy w hw hw' ξ η => ?_⟩
  · have := h.mono y (Ioo_subset_Ioo_right hδ hs) (Ioo_subset_Ioo_right hδ ht) hst
    have h₁ : (K' - K) * s ^ 2 ≤ (K' - K) * t ^ 2 := by
      have := hs.1
      gcongr
    beta_reduce at this ⊢
    linarith
  · refine le_trans ?_ (h.hess c y hy w hw (hw'.trans_le hδ) ξ η)
    have hd : DifferentiableAt ℝ (Ψ y) ‖w‖ := by
      have ho : IsOpen (c.e.target ×ˢ {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < δ}) := c.e.open_target.prod
        ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
      have h₁ := (((h.smooth c).contDiffAt (x := (c.e y, ((‖w‖ : ℝ) : ℂ))) (ho.mem_nhds ⟨c.e.map_source hy, by
        simpa using hw, by simpa using hw'.trans_le hδ⟩)).differentiableAt (by simp)).comp (f := fun t : ℝ => (c.e y, (t : ℂ)))
          ‖w‖ ((differentiableAt_const _).prodMk Complex.ofRealCLM.differentiableAt)
      refine h₁.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hw] with t ht
      simp [c.e.left_inv hy, abs_of_pos (show 0 < t from ht)]
    have e (L : ℝ) : deriv (fun t => Ψ y t + L * t ^ 2) ‖w‖ = deriv (Ψ y) ‖w‖ + L * (2 * ‖w‖) := by
      simpa using (hd.hasDerivAt.fun_add ((hasDerivAt_pow 2 ‖w‖).const_mul L)).deriv
    have h0 : 0 ≤ deriv (fun t => Ψ y t + K * t ^ 2) ‖w‖ := by
      have := (h.mono y).derivWithin_nonneg (x := ‖w‖)
      rwa [derivWithin_of_isOpen isOpen_Ioo ⟨hw, hw'.trans_le hδ⟩] at this
    have h1 : deriv (fun t => Ψ y t + K * t ^ 2) ‖w‖ ≤ deriv (fun t => Ψ y t + K' * t ^ 2) ‖w‖ := by
      rw [e, e]
      gcongr
    have ha0 := kaehler_nonneg ha c hy ξ.ofLp
    have hA0 := h.A_nonneg
    have hA' := hA0.trans hA
    gcongr

end Mono

def logAbs (z : Fin 1 → ℂ) : EReal := if z 0 = 0 then ⊥ else (Real.log ‖z 0‖ : ℝ)

theorem trunc_logAbs (κ : ℝ) (z : Fin 1 → ℂ) :
    (max (logAbs z) ((-κ : ℝ) : EReal)).toReal = Real.log (max ‖z 0‖ (Real.exp (-κ))) := by
  unfold logAbs
  split_ifs with h
  · simp [h, (Real.exp_pos _).le]
  · rw [toReal_max]
    rcases le_total ‖z 0‖ (Real.exp (-κ)) with h' | h'
    · rw [max_eq_right h', Real.log_exp, max_eq_right ((Real.log_le_iff_le_exp (norm_pos_iff.2 h)).2 h')]
    · rw [max_eq_left h', max_eq_left ((Real.le_log_iff_exp_le (norm_pos_iff.2 h)).2 h')]

theorem isPshExt_logAbs : IsPshExt univ logAbs := by
  have hc (κ : ℝ) : Continuous fun z : Fin 1 → ℂ => Real.log (max ‖z 0‖ (Real.exp (-κ))) :=
    Continuous.log (by fun_prop) fun z => ((Real.exp_pos _).trans_le (le_max_right _ _)).ne'
  refine ⟨fun z _ => ?_, ?_, fun z _ => ?_, fun κ => ?_⟩
  · unfold logAbs
    split_ifs
    · simp
    · exact EReal.coe_ne_top _
  · intro z _ y hy
    obtain ⟨b, hb, hb'⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    have hm (x : Fin 1 → ℂ) : max (logAbs x) ((-(1 - b) : ℝ) : EReal) =
        (Real.log (max ‖x 0‖ (Real.exp (-(1 - b)))) : ℝ) := by
      rw [← trunc_logAbs, EReal.coe_toReal]
      · refine (max_lt ?_ (EReal.coe_lt_top _)).ne
        unfold logAbs
        split_ifs
        · simp
        · exact EReal.coe_lt_top _
      · exact ((EReal.bot_lt_coe _).trans_le (le_max_right _ _)).ne'
    have h₁ : Real.log (max ‖z 0‖ (Real.exp (-(1 - b)))) < b := by
      rw [← EReal.coe_lt_coe_iff, ← hm]
      exact max_lt hb (EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((isOpen_lt (hc (1 - b)) continuous_const).mem_nhds h₁)] with x hx
    refine lt_trans ((le_max_left _ _).trans_lt ((hm x).trans_lt (EReal.coe_lt_coe_iff.2 hx))) hb'
  · have hd : Dense {z : Fin 1 → ℂ | z ≠ 0} := dense_compl_singleton (0 : Fin 1 → ℂ)
    refine closure_mono (fun x hx => (⟨trivial, ?_⟩ : x ∈ {z ∈ univ | logAbs z ≠ ⊥})) (hd z)
    have : x 0 ≠ 0 := fun h => hx (funext fun i => by rwa [Subsingleton.elim i 0])
    simp [logAbs, this]
  · simp only [trunc_logAbs]
    refine ⟨(hc κ).continuousOn.upperSemicontinuousOn, fun z w _ => ?_⟩
    have hi : CircleIntegrable (fun ζ : ℂ => Real.log (max ‖(z + ζ • w) 0‖ (Real.exp (-κ)))) 0 1 :=
      ((hc κ).comp (f := fun ζ : ℂ => z + ζ • w) (by fun_prop)).continuousOn.circleIntegrable zero_le_one
    refine ⟨hi, ?_⟩
    beta_reduce
    rcases le_total ‖z 0‖ (Real.exp (-κ)) with h' | h'
    · rw [max_eq_right h', ← Real.circleAverage_const (Real.log (Real.exp (-κ))) 0 1]
      exact Real.circleAverage_mono (circleIntegrable_const _ _ _) hi fun ζ _ =>
        Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    · rw [max_eq_left h']
      have hz : z 0 ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le h')
      have hg : AnalyticOnNhd ℂ (fun ζ : ℂ => (z + ζ • w) 0) (Metric.closedBall 0 1) := fun ζ _ => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        fun_prop
      have h0 : (fun ζ : ℂ => (z + ζ • w) 0) 0 ≠ 0 := by simpa using hz
      have h1 := hg.preimage_zero_mem_codiscreteWithin h0 (Metric.mem_closedBall_self zero_le_one)
        (Metric.isConnected_closedBall zero_le_one)
      have h3 : (fun ζ : ℂ => (z + ζ • w) 0) ⁻¹' {0}ᶜ ∈ codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|) :=
        codiscreteWithin_mono (by simpa using Metric.sphere_subset_closedBall) h1
      have hne : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Icc 0 (2 * Real.pi))), (z + circleMap 0 1 t • w) 0 ≠ 0 :=
        ae_restrict_le_codiscreteWithin measurableSet_Icc
          (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete one_ne_zero h3))
      have hl : CircleIntegrable (fun ζ : ℂ => Real.log ‖(z + ζ • w) 0‖) 0 1 :=
        MeromorphicOn.circleIntegrable_log_norm
          (hg.mono (by simpa using Metric.sphere_subset_closedBall)).meromorphicOn
      have hJ := log_norm_le_circleAverage_log_norm hg h0
      simp only [zero_smul, add_zero] at hJ
      refine hJ.trans ?_
      simp only [Real.circleAverage, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_ae_restrict (by positivity) hl hi ?_) (by positivity)
      filter_upwards [hne] with t ht
      exact Real.log_le_log (norm_pos_iff.2 ht) (le_max_left _ _)

section Ends

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ}

theorem not_isPshExt_dip : ¬ IsPshExt (univ : Set (Fin 1 → ℂ)) fun z => if z = 0 then ⊥ else 0 := fun h => by
  have h₁ := h.2.1 0 trivial 0 (by simp)
  rw [nhdsWithin_univ] at h₁
  obtain ⟨z, hz, hz'⟩ := (dense_compl_singleton (0 : Fin 1 → ℂ)).inter_nhds_nonempty h₁
  have : z ≠ 0 := hz
  simp [this] at hz'

theorem not_isPshExt_spike : ¬ IsPshExt (univ : Set (Fin 1 → ℂ)) fun z => if z = 0 then 1 else 0 := fun h => by
  have h₁ := ((h.2.2.2 0).2 0 1 fun _ _ => trivial).2
  have e : EqOn (fun ζ : ℂ => (max (if (0 : Fin 1 → ℂ) + ζ • (1 : Fin 1 → ℂ) = 0 then (1 : EReal) else 0)
      ((-0 : ℝ) : EReal)).toReal) (fun _ => 0) (Metric.sphere 0 |1|) := fun ζ hζ => by
    have : ζ ≠ 0 := by rintro rfl; simp at hζ
    simp [this]
  rw [Real.circleAverage_congr_sphere e, Real.circleAverage_const] at h₁
  norm_num at h₁

theorem conclusion_const_full {d : ℕ} [SmoothOfRelativeDimension d p] {R : AnRead p σ d} {a θ : ChartForm p σ d}
    (ha : IsKaehlerForm R a) (hθ : IsClosedForm R θ) (E : ChartMap p σ d) (r : ℝ)
    (h : IsFormPsh R θ fun _ => (r : EReal)) :
    ∃ A K δ : ℝ, IsRegConst a θ (rho a E fun _ => (r : EReal).toReal) A K δ ∧
      (∀ y, ∀ t ∈ Ioo 0 δ, (r : EReal) ≤ ((rho a E (fun _ => (r : EReal).toReal) y t + K * t ^ 2 : ℝ) : EReal)) ∧
      ∀ y, Tendsto (fun t => ((rho a E (fun _ => (r : EReal).toReal) y t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (r : EReal)) :=
  ⟨0, 0, 1, conclusion_const ha hθ E r h, fun y t _ => by simp [rho_const ha], fun y => by simp [rho_const ha]⟩

theorem conclusion_dim_zero [SmoothOfRelativeDimension 0 p] {a θ : ChartForm p σ 0} {E : ChartMap p σ 0}
    {v : CxPts p σ → EReal} (ha : IsKaehlerForm (AnRead.all p σ 0) a) (hE : IsExph a E)
    (hθ : IsClosedForm (AnRead.all p σ 0) θ) (hv : IsFormPsh (AnRead.all p σ 0) θ v) :
    ∃ A K δ : ℝ, IsRegConst a θ (rho a E fun y => (v y).toReal) A K δ ∧
      (∀ y, ∀ t ∈ Ioo 0 δ, v y ≤ ((rho a E (fun y => (v y).toReal) y t + K * t ^ 2 : ℝ) : EReal)) ∧
      ∀ y, Tendsto (fun t => ((rho a E (fun y => (v y).toReal) y t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (v y)) := by
  have e (y t) : rho a E (fun y => (v y).toReal) y t = (v y).toReal := by
    rw [← rho_zero ha hE (fun y => (v y).toReal) y]
    simp only [rho, rhoIn]
    congr 1
    funext ξ
    rw [Subsingleton.elim (t • ξ) ((0 : ℝ) • ξ)]
  have hf (y) : (((v y).toReal : ℝ) : EReal) = v y := by
    obtain ⟨W, φ, hW, hφ⟩ := hθ y
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := 0) y
    have h := hv W φ hφ c
    have hl : c.finChart.symm (c.finChart y) = y := c.finChart.left_inv hc
    have hm : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' W :=
      ⟨c.finChart.map_source hc, by rwa [mem_preimage, hl]⟩
    have h₁ := h.1 _ hm
    obtain ⟨z, -, h₂⟩ := closure_nonempty_iff.1 ⟨_, h.2.2.1 hm⟩
    rw [Subsingleton.elim z (c.finChart y)] at h₂
    simp only [hl] at h₁ h₂
    refine EReal.coe_toReal ?_ ?_
    · rintro h'
      simp [h'] at h₁
    · rintro h'
      simp [h'] at h₂
  have ec (c : AlgChart p σ 0) : (fun q : V 0 × ℂ => rho a E (fun y => (v y).toReal) (c.e.symm q.1) ‖q.2‖) =
      fun _ => (v (c.e.symm 0)).toReal := funext fun q => by rw [e, Subsingleton.elim q.1 0]
  refine ⟨0, 0, 1, ⟨le_rfl, le_rfl, one_pos, fun c => ?_, fun y s _ t _ _ => by simp [e], fun c y hy w _ _ ξ η => ?_⟩,
    fun y t _ => by simp [e, hf], fun y => by simp [e, hf]⟩
  · rw [ec]
    exact contDiffOn_const
  · obtain ⟨W, φ, hW, hφ⟩ := hθ y
    have e' (r : ℝ) : dbar (fun _ : V 0 × ℂ => (r : ℂ)) = fun _ => 0 := funext fun _ => dbar_const _ _
    rw [ec, leviForm, ddbar, e', del_const, hφ.2.2 c y hy hW]
    simp [ddcForm, AlgChart.levi, leviV]

end Ends

end GlobalTheory.RegularisationModel

end
