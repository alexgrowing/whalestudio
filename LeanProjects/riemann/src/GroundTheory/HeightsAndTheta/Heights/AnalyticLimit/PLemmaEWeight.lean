import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEWeight
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul levi_re_analytic levi_zero)
open ReciprocityTheory.AnForm.A (regMax regMax_thm regMaxLevi_thm tmax le_tmax tmax_le)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh logNormSec)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem rSec_local {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L)
    (hs : IsSection A L s) {q : X} (hq : q ∈ secOpen s) :
    ∃ V : Set X, IsOpen V ∧ q ∈ V ∧ V ⊆ L.U q ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
      ∀ z ∈ V, rSec L s z = Real.exp 1 - 2 * (G z).re + 2 * L.φ q z := by
  have hW : IsOpen (L.U q ∩ secOpen s) := (L.isOpen_U q).inter (isOpen_secOpen hL hs)
  have hg : A.HoloOn (L.U q ∩ secOpen s) (s q) := fun j =>
    (hs.1 q j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  have hne : ∀ z ∈ L.U q ∩ secOpen s, s q z ≠ 0 := by
    intro z hz h0
    have h := hs.2 z q z ⟨L.mem_U z, hz.1⟩
    rw [h0, norm_zero, zero_mul] at h
    exact hz.2 (norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (Real.exp_ne_zero _)))
  obtain ⟨V, hV, hqV, hVW, G, hG, hEq⟩ :=
    LogNormHolo.full D A _ (s q) hW hg hne q ⟨L.mem_U q, hq⟩
  refine ⟨V, hV, hqV, fun z hz => (hVW hz).1, G, hG, fun z hz => ?_⟩
  have h := hs.2 z q z ⟨L.mem_U z, (hVW hz).1⟩
  unfold rSec logNormSec
  rw [h, Real.log_mul (norm_ne_zero_iff.2 (hne z (hVW hz))) (Real.exp_ne_zero _), Real.log_exp,
    hEq z hz]
  ring

theorem rSec_chart {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L)
    (hs : IsSection A L s) (k : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart k).target)
    (hq : (A.chart k).symm y ∈ secOpen s) :
    ContDiffAt ℝ ∞ (rSec L s ∘ (A.chart k).symm) y ∧ ∀ v : Fin D → ℂ,
      levi (rSec L s ∘ (A.chart k).symm) y v =
        2 * levi (L.φ ((A.chart k).symm y) ∘ (A.chart k).symm) y v := by
  set q := (A.chart k).symm y
  obtain ⟨V, hV, hqV, hVU, G, hG, hEq⟩ := rSec_local hL hs hq
  have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' V) :=
    (A.chart k).isOpen_inter_preimage_symm hV
  have hyO : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V := ⟨hy, hqV⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart k).symm) y := hG k y hyO
  have hRe : ContDiffAt ℝ ∞ (fun y' => (G ((A.chart k).symm y')).re) y := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := ∞)).contDiffAt.comp y
      ((hGa.contDiffAt (n := ∞)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have hφ : ContDiffAt ℝ ∞ (L.φ q ∘ (A.chart k).symm) y :=
    (hL.1 q k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm (L.isOpen_U q)).mem_nhds
      ⟨hy, L.mem_U q⟩)
  have hev : rSec L s ∘ (A.chart k).symm =ᶠ[𝓝 y] fun y' =>
      (Real.exp 1 + (-2) * (G ((A.chart k).symm y')).re) + 2 * (L.φ q ∘ (A.chart k).symm) y' := by
    filter_upwards [hO.mem_nhds hyO] with y' hy'
    simp only [Function.comp]
    rw [hEq _ hy'.2]
    ring
  have hc : ContDiffAt ℝ ∞ (fun y' => Real.exp 1 + (-2) * (G ((A.chart k).symm y')).re) y :=
    contDiffAt_const.add (contDiffAt_const.mul hRe)
  refine ⟨(hc.add (contDiffAt_const.mul hφ)).congr_of_eventuallyEq hev, fun v => ?_⟩
  have h1 := levi_add_smul (f := fun y' => Real.exp 1 + (-2) * (G ((A.chart k).symm y')).re)
    (g := L.φ q ∘ (A.chart k).symm) 2 (hc.of_le ReciprocityTheory.AnForm.A.two_le_inf)
    (hφ.of_le ReciprocityTheory.AnForm.A.two_le_inf) v
  have h2 := levi_add_smul (f := fun _ : Fin D → ℂ => Real.exp 1)
    (g := fun y' => (G ((A.chart k).symm y')).re) (-2) contDiffAt_const
    (hRe.of_le ReciprocityTheory.AnForm.A.two_le_inf) v
  have h0 : levi (fun y' => (G ((A.chart k).symm y')).re) y v = 0 := levi_re_analytic hGa v
  rw [levi_congr hev v, h1, h2, levi_const, h0]
  ring

theorem levi_kaehler_nonneg {A : FinHolAtlas D X} (Om : KaehlerForm A) (x : X) (k : Fin A.n)
    {y : Fin D → ℂ} (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' Om.pot.U x)
    (v : Fin D → ℂ) : 0 ≤ levi (Om.pot.φ x ∘ (A.chart k).symm) y v := by
  rcases eq_or_ne v 0 with h0 | h0
  · rw [h0, levi_zero]
  · exact (Om.pos x k y hy v h0).le

theorem exists_levi_weight_constant [CompactSpace X] {A : FinHolAtlas D X} (Om : KaehlerForm A) {L : LocPot X}
    (hL : IsPotential A L) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (k : Fin A.n) (y : Fin D → ℂ),
      y ∈ (A.chart k).target → ∀ v : Fin D → ℂ,
        2 * c₀ * levi (L.φ ((A.chart k).symm y) ∘ (A.chart k).symm) y v ≤
          levi (Om.pot.φ ((A.chart k).symm y) ∘ (A.chart k).symm) y v := by
  obtain ⟨M, hM0, hM⟩ := levi_abs_le_global A isCompact_univ L Om.pot hL Om.isPot Om.pos
  refine ⟨1 / (2 * (M + 1)), by positivity, fun k y hy v => ?_⟩
  set q := (A.chart k).symm y
  have h1 := hM q k y ⟨hy, L.mem_U q, Om.pot.mem_U q⟩ v
  have h2 := levi_kaehler_nonneg Om q k ⟨hy, Om.pot.mem_U q⟩ v
  have h3 := le_abs_self (levi (L.φ q ∘ (A.chart k).symm) y v)
  have hM1 : 0 < M + 1 := by linarith
  rw [show 2 * (1 / (2 * (M + 1))) = (M + 1)⁻¹ by field_simp, inv_mul_le_iff₀ hM1]
  nlinarith

theorem eventually_le_rSec {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) {c₀ : ℝ} (hc₀ : 0 < c₀) {q : X}
    (hq : q ∉ secOpen s) (B : ℝ) : ∀ᶠ z in 𝓝 q, z ∈ secOpen s → B ≤ c₀ * rSec L s z := by
  set δ := Real.exp ((Real.exp 1 - B / c₀) / 2)
  have hq0 : ‖s q q‖ * Real.exp (-L.φ q q) = 0 := by
    have h : s q q = 0 := by
      by_contra h
      exact hq h
    simp [h]
  have hT := (continuous_normSec hL hs).continuousAt (x := q)
  have hev : ∀ᶠ z in 𝓝 q, ‖s z z‖ * Real.exp (-L.φ z z) < δ :=
    hT.eventually (gt_mem_nhds (by
      show ‖s q q‖ * Real.exp (-L.φ q q) < δ
      rw [hq0]
      exact Real.exp_pos _))
  filter_upwards [hev] with z hz hzY
  have hpos : 0 < ‖s z z‖ * Real.exp (-L.φ z z) :=
    mul_pos (norm_pos_iff.2 hzY) (Real.exp_pos _)
  have hlog : logNormSec L s z < (Real.exp 1 - B / c₀) / 2 := by
    have := Real.log_lt_log hpos hz
    rwa [Real.log_exp] at this
  have hr : B / c₀ < rSec L s z := by
    unfold rSec
    linarith
  rw [div_lt_iff₀ hc₀] at hr
  linarith

def eWeightPair (L : LocPot X) (s : X → X → ℂ) (c₀ l : ℝ) (z : X) : Fin 2 → ℝ :=
  ![-(c₀ * rSec L s z), -l]

open Classical in

def eWeight (L : LocPot X) (s : X → X → ℂ) (c₀ l : ℝ) (z : X) : ℝ :=
  if z ∈ secOpen s then regMax 1 (eWeightPair L s c₀ l z) - 1 else -l - 1

theorem eWeight_eventually_const {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) {c₀ : ℝ} (hc₀ : 0 < c₀) (l : ℝ) {q : X}
    (hq : q ∉ secOpen s) : eWeight L s c₀ l =ᶠ[𝓝 q] fun _ => -l - 1 := by
  obtain ⟨-, -, -, -, heq, -⟩ := (regMax_thm (Fin 2)).1 1 one_pos
  filter_upwards [eventually_le_rSec hL hs hc₀ hq (l + 1)] with z hz
  by_cases hzY : z ∈ secOpen s
  · have h := hz hzY
    rw [eWeight, if_pos hzY, heq (eWeightPair L s c₀ l z) 1 fun j hj => ?_]
    · rfl
    · fin_cases j
      · show -(c₀ * rSec L s z) + 1 ≤ -l
        linarith
      · exact absurd rfl hj
  · rw [eWeight, if_neg hzY]

theorem eWeight_smooth {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) {c₀ : ℝ} (hc₀ : 0 < c₀) (l : ℝ) :
    A.Smooth (eWeight L s c₀ l) := by
  obtain ⟨hcd, -⟩ := (regMax_thm (Fin 2)).1 1 one_pos
  intro k y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have ht : Tendsto (A.chart k).symm (𝓝 y) (𝓝 ((A.chart k).symm y)) :=
    (A.chart k).continuousAt_symm hy.1
  by_cases hq : (A.chart k).symm y ∈ secOpen s
  · have hev : eWeight L s c₀ l ∘ (A.chart k).symm =ᶠ[𝓝 y]
        fun y' => regMax 1 (fun j => eWeightPair L s c₀ l ((A.chart k).symm y') j) - 1 := by
      filter_upwards [ht.eventually ((isOpen_secOpen hL hs).mem_nhds hq)] with y' hy'
      have hy'' : (A.chart k).symm y' ∈ secOpen s := hy'
      simp only [Function.comp, eWeight, if_pos hy'']
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine (hcd.contDiffAt.comp y (contDiffAt_pi.2 fun j => ?_)).sub contDiffAt_const
    fin_cases j
    · show ContDiffAt ℝ ∞ (fun y' => -(c₀ * rSec L s ((A.chart k).symm y'))) y
      exact (contDiffAt_const.mul (rSec_chart hL hs k hy.1 hq).1).neg
    · exact contDiffAt_const
  · exact contDiffAt_const.congr_of_eventuallyEq
      (ht.eventually (eWeight_eventually_const hL hs hc₀ l hq))

theorem eWeight_psh {A : FinHolAtlas D X} (Om : KaehlerForm A) {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc : ∀ (k : Fin A.n) (y : Fin D → ℂ), y ∈ (A.chart k).target → ∀ v : Fin D → ℂ,
        2 * c₀ * levi (L.φ ((A.chart k).symm y) ∘ (A.chart k).symm) y v ≤
          levi (Om.pot.φ ((A.chart k).symm y) ∘ (A.chart k).symm) y v) (l : ℝ) :
    IsPsh A (potForm Om.pot (eWeight L s c₀ l)) := by
  obtain ⟨hcd, -⟩ := (regMax_thm (Fin 2)).1 1 one_pos
  intro x k y hy v
  have hyO : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' Om.pot.U x := ⟨hy.1, hy.2.1⟩
  set q := (A.chart k).symm y with hqdef
  have ht : Tendsto (A.chart k).symm (𝓝 y) (𝓝 q) := (A.chart k).continuousAt_symm hy.1
  have hO2 : ContDiffAt ℝ 2 (Om.pot.φ x ∘ (A.chart k).symm) y :=
    ((Om.isPot.1 x k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm
      (Om.pot.isOpen_U x)).mem_nhds hyO)).of_le ReciprocityTheory.AnForm.A.two_le_inf
  have hOnn := levi_kaehler_nonneg Om x k hyO v
  show 0 ≤ levi (fun y' => Om.pot.φ x ((A.chart k).symm y') +
    eWeight L s c₀ l ((A.chart k).symm y')) y v
  by_cases hq : q ∈ secOpen s
  · have hU : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' secOpen s) :=
      (A.chart k).isOpen_inter_preimage_symm (isOpen_secOpen hL hs)
    set u : Fin 2 → (Fin D → ℂ) → ℝ := fun j y' => eWeightPair L s c₀ l ((A.chart k).symm y') j
      with hudef
    have hu : ∀ j, ContDiffOn ℝ 2 (u j) ((A.chart k).target ∩ (A.chart k).symm ⁻¹' secOpen s) := by
      intro j
      fin_cases j
      · intro y' hy'
        exact ((contDiffAt_const.mul (rSec_chart hL hs k hy'.1 hy'.2).1).neg.of_le
          ReciprocityTheory.AnForm.A.two_le_inf).contDiffWithinAt
      · exact contDiffOn_const
    have hh : ContDiffAt ℝ 2 (fun y' => regMax 1 (fun j => u j y')) y :=
      (hcd.of_le ReciprocityTheory.AnForm.A.two_le_inf).contDiffAt.comp y (contDiffAt_pi.2 fun j =>
        (hu j).contDiffAt (hU.mem_nhds ⟨hy.1, hq⟩))
    have hev : (fun y' => Om.pot.φ x ((A.chart k).symm y') +
        eWeight L s c₀ l ((A.chart k).symm y')) =ᶠ[𝓝 y]
        fun y' => ((Om.pot.φ x ∘ (A.chart k).symm) y' + 1 * regMax 1 (fun j => u j y')) + (-1) := by
      filter_upwards [ht.eventually ((isOpen_secOpen hL hs).mem_nhds hq)] with y' hy'
      have hy'' : (A.chart k).symm y' ∈ secOpen s := hy'
      simp only [Function.comp, eWeight, if_pos hy'', hudef]
      ring
    have hg := regMaxLevi_thm D (Fin 2) 1 _ u hU one_pos hu y ⟨hy.1, hq⟩ v
      (-levi (Om.pot.φ x ∘ (A.chart k).symm) y v) fun j => ?_
    · rw [levi_congr hev v, levi_add_const, levi_add_smul 1 hO2 hh v]
      linarith
    · fin_cases j
      · show -levi (Om.pot.φ x ∘ (A.chart k).symm) y v ≤
          levi (fun y' => -(c₀ * rSec L s ((A.chart k).symm y'))) y v
        have hF := rSec_chart hL hs k hy.1 hq
        have e1 : (fun y' => -(c₀ * rSec L s ((A.chart k).symm y'))) =
            fun y' => (0 : ℝ) + (-c₀) * (rSec L s ∘ (A.chart k).symm) y' := by
          funext y'
          simp only [Function.comp]
          ring
        have hb := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe.levi_base_indep Om.isPot
          (ψ := A.chart k) (fun m => ⟨A.holo m k, A.holo k m⟩) (x := x) (x' := q) (p := q)
          hy.2.1 (Om.pot.mem_U q) ((A.chart k).map_target hy.1) v
        rw [hqdef, (A.chart k).right_inv hy.1] at hb
        have h1 := levi_add_smul (f := fun _ : Fin D → ℂ => (0 : ℝ))
          (g := rSec L s ∘ (A.chart k).symm) (-c₀) contDiffAt_const
          (hF.1.of_le ReciprocityTheory.AnForm.A.two_le_inf) v
        rw [e1, h1, levi_const, hF.2 v, hb]
        have := hc k y hy.1 v
        linarith
      · show -levi (Om.pot.φ x ∘ (A.chart k).symm) y v ≤ levi (fun _ => -l) y v
        rw [levi_const]
        linarith
  · have hev : (fun y' => Om.pot.φ x ((A.chart k).symm y') +
        eWeight L s c₀ l ((A.chart k).symm y')) =ᶠ[𝓝 y]
        fun y' => (Om.pot.φ x ∘ (A.chart k).symm) y' + (-l - 1) := by
      filter_upwards [ht.eventually (eWeight_eventually_const hL hs hc₀ l hq)] with y' hy'
      simp only [Function.comp] at hy' ⊢
      rw [hy']
    rw [levi_congr hev v, levi_add_const]
    exact hOnn

theorem eWeight_bounds {L : LocPot X} {s : X → X → ℂ} (c₀ l : ℝ) {z : X} (hz : z ∈ secOpen s) :
    min (c₀ * rSec L s z) l ≤ -eWeight L s c₀ l z ∧ -eWeight L s c₀ l z ≤ c₀ * rSec L s z + 1 := by
  obtain ⟨-, -, -, hbd, -⟩ := (regMax_thm (Fin 2)).1 1 one_pos
  obtain ⟨h1, h2⟩ := hbd (eWeightPair L s c₀ l z)
  have h0 : -(c₀ * rSec L s z) ≤ tmax (eWeightPair L s c₀ l z) :=
    le_tmax (eWeightPair L s c₀ l z) (0 : Fin 2)
  have hm : tmax (eWeightPair L s c₀ l z) ≤ -min (c₀ * rSec L s z) l := tmax_le fun j => by
    fin_cases j
    · show -(c₀ * rSec L s z) ≤ -min (c₀ * rSec L s z) l
      exact neg_le_neg (min_le_left _ _)
    · show -l ≤ -min (c₀ * rSec L s z) l
      exact neg_le_neg (min_le_right _ _)
  rw [eWeight, if_pos hz]
  constructor <;> linarith

theorem LemmaEWeight.proof : LemmaEWeight.Statement := by
  intro X _ _ _ D A Om L s hL hs
  obtain ⟨c₀, hc₀, hc⟩ := exists_levi_weight_constant Om hL
  refine ⟨c₀, hc₀, fun l _ => ⟨eWeight L s c₀ l, eWeight_smooth hL hs hc₀ l,
    eWeight_psh Om hL hs hc₀ hc l, fun x hx => eWeight_bounds c₀ l hx, fun x hx => ?_⟩⟩
  rw [eWeight, if_neg hx]
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
