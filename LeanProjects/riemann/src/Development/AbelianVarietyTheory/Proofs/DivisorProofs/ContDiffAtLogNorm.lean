import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableOnOfNormLeSumAbsLogAddLogLog

open Filter Topology MeasureTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O
open ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Mean4O

namespace BdSec

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}

theorem levi_log_norm {G : (Fin e → ℂ) → ℂ} {z : Fin e → ℂ} (hG : AnalyticAt ℂ G z) (h0 : G z ≠ 0)
    (w : Fin e → ℂ) : levi (fun y => Real.log ‖G y‖) z w = 0 := by
  have h1 : AnalyticAt ℂ (fun y => Complex.log (G y / G z)) z :=
    (hG.div_const (c := G z)).clog (by simp [div_self h0])
  have h2 : (fun y => Real.log ‖G y‖ - Real.log ‖G z‖) =ᶠ[𝓝 z] fun y => (Complex.log (G y / G z)).re := by
    filter_upwards [hG.continuousAt.eventually_ne h0] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hy) (norm_ne_zero_iff.2 h0)]
  rw [← levi_sub_const _ (Real.log ‖G z‖), levi_congr h2, levi_re_analytic h1]

theorem contDiffAt_log_norm {G : (Fin e → ℂ) → ℂ} {z : Fin e → ℂ} (hG : AnalyticAt ℂ G z) (h0 : G z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log ‖G y‖) z :=
  (((hG.restrictScalars (𝕜 := ℝ)).contDiffAt).norm ℝ h0).log (norm_ne_zero_iff.2 h0)

theorem contDiffAt_pot {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) y :=
  (hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)

theorem mem_interior_iff (hS : IsSection A L s) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x) :
    (A.chart j).symm y ∈ interior (bdry s) ↔ ∀ᶠ z in 𝓝 y, s x ((A.chart j).symm z) = 0 := by
  rw [mem_interior_iff_mem_nhds, ← (A.chart j).symm.map_nhds_eq hy.1, mem_map]
  refine eventually_congr ?_
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (L.isOpen_U x)).mem_nhds hy] with z hz
  exact bdry_iff hS hz.2

theorem interior_bdry [ConnectedSpace X] (hS : IsSection A L s) (h : bdry s ≠ Set.univ) :
    interior (bdry s) = ∅ := by
  have hc : IsClosed (interior (bdry s)) := by
    rw [← closure_subset_iff_isClosed]
    intro p hp
    obtain ⟨j, hj⟩ := A.cover p
    have hO := (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U p)
    have hpO : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p :=
      ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using L.mem_U p⟩
    obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hO _ hpO
    obtain ⟨q, ⟨hq, hqB⟩, hqi⟩ := mem_closure_iff.1 hp _
      ((A.chart j).isOpen_inter_preimage (Metric.isOpen_ball (x := A.chart j p) (ε := ε)))
      ⟨hj, Metric.mem_ball_self hε⟩
    rw [← (A.chart j).left_inv hq, mem_interior_iff hS p j (hB hqB)] at hqi
    have h1 := ((hS.1 p j).mono hB).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball _ _).isPreconnected hqB hqi
    rw [← (A.chart j).left_inv hj, mem_interior_iff hS p j hpO]
    filter_upwards [Metric.ball_mem_nhds _ hε] with z hz using h1 hz
  rcases isClopen_iff.1 ⟨hc, isOpen_interior⟩ with h1 | h1
  · exact h1
  · exact absurd (interior_eq_univ.1 h1) h

theorem bdry_null_chart (hS : IsSection A L s) (h : interior (bdry s) = ∅) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' bdry s) = 0 := by
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(bdry_iff hS hzU).2 (hz 0), hzU⟩
  have := analyticNull A (bdry s) hAn h j
  rwa [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this

theorem continuous_norm_sec (hL : IsPotential A L) (hS : IsSection A L s) :
    Continuous fun y => ‖s y y‖ * Real.exp (-L.φ y y) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc := continuousAt_of_holoOn A (hS.1 y) (L.mem_U y)
  have hφ := continuousAt_of_smoothOn A (L.isOpen_U y) (hL.1 y) (L.mem_U y)
  refine (hc.norm.mul (Real.continuous_exp.continuousAt.comp hφ.neg)).congr ?_
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  exact hS.2 y z z ⟨hz, L.mem_U z⟩

variable {r : X → ℝ}

theorem toBot (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) :
    ToBot (bdry s) fun x => -r x := by
  intro a
  have hc := isClosed_le (continuous_const (y := Real.exp ((Real.exp 1 - a) / 2))) (continuous_norm_sec hL hS)
  refine (closure_minimal ?_ hc).trans ?_
  · rintro x ⟨hx, hxa⟩
    have hx' : s x x ≠ 0 := hx
    simp only [hr x hx, rW, logNormSec] at hxa
    exact (Real.le_log_iff_exp_le (mul_pos (norm_pos_iff.2 hx') (Real.exp_pos _))).1 (by linarith)
  · intro x hx hx0
    have hx' : s x x = 0 := hx0
    rw [Set.mem_setOf_eq, hx', norm_zero, zero_mul] at hx
    exact (Real.exp_pos _).not_ge hx

theorem local_eq (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) {x z : X} (hz : z ∈ L.U x)
    (h0 : s x z ≠ 0) : r z = Real.exp 1 - 2 * (Real.log ‖s x z‖ - L.φ x z) := by
  rw [hr z fun h => h0 ((bdry_iff hS hz).1 h), rW, logNormSecLocal A L s x z hS hz h0]

theorem local_eventuallyEq (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (h0 : (A.chart j).symm y ∉ bdry s) :
    ∀ᶠ z in 𝓝 y, r ((A.chart j).symm z) = Real.exp 1 - 2 *
      (Real.log ‖s ((A.chart j).symm y) ((A.chart j).symm z)‖ - L.φ ((A.chart j).symm y) ((A.chart j).symm z)) := by
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y) := ⟨hy, L.mem_U _⟩
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (L.isOpen_U _)).mem_nhds hm,
    (hS.1 _ j y hm).continuousAt.eventually_ne h0] with z hz hz0
  exact local_eq hS hr hz.2 hz0

theorem smoothOn (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) :
    A.SmoothOn (bdry s)ᶜ r := by
  intro j y hy
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y) := ⟨hy.1, L.mem_U _⟩
  exact ((contDiffAt_const.sub (contDiffAt_const.mul ((contDiffAt_log_norm (hS.1 _ j y hm) hy.2).sub
    (contDiffAt_pot hL _ j hm)))).congr_of_eventuallyEq
    (local_eventuallyEq hS hr j hy.1 hy.2)).contDiffWithinAt

theorem mIntegrable (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x)
    (h : interior (bdry s) = ∅) {Φ : Fin e → LocPot X} (hΦ : ∀ i, IsPotential A (Φ i)) :
    MIntegrable A Φ (cut (bdry s) Set.univ r) := by
  intro j K hKt hK
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y hy => ?_) hK
  set x := (A.chart j).symm y with hx
  have hO := (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U x)
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x := ⟨hKt hy, L.mem_U _⟩
  obtain ⟨B, hBn, hB, hBc⟩ := local_compact_nhds (hO.mem_nhds hm)
  refine ⟨B, mem_nhdsWithin_of_mem_nhds hBn, ?_⟩
  obtain ⟨h1, h2⟩ := locallyIntegrableOn_log_norm_of_frequently_ne_zero volume hO (hS.1 x j).differentiableOn
    fun z hz hev => by
      have := (mem_interior_iff hS x j hz).2 (hev.mono fun _ h => not_not.1 h)
      rw [h] at this
      exact this
  have h3 := h2.integrableOn_compact_subset hB hBc
  have h4 : IntegrableOn (L.φ x ∘ (A.chart j).symm) B :=
    ((hL.1 x j).continuousOn.mono hB).integrableOn_compact hBc
  have h5 : IntegrableOn (fun _ => Real.exp 1) B := continuousOn_const.integrableOn_compact hBc
  have h6 : IntegrableOn (fun z => Real.exp 1 - 2 * (Real.log ‖s x ((A.chart j).symm z)‖ -
      L.φ x ((A.chart j).symm z))) B := h5.sub ((h3.sub h4).const_mul 2)
  refine (h6.mul_continuousOn ((locDensCont A Φ hΦ j).mono (hB.trans Set.inter_subset_left)) hBc).congr ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hB h1, ae_restrict_mem hBc.measurableSet] with z hz hzB
  have hzU := (hB hzB).2
  rw [cut, Set.indicator_of_mem (show _ ∈ Set.univ ∩ (bdry s)ᶜ from
    ⟨trivial, fun h => hz ((bdry_iff hS hzU).1 h)⟩), local_eq hS hr hzU hz]

theorem exists_pshOff [CompactSpace X] [T2Space X] {Om : LocPot X} (hO : IsPotential A Om) (hP : IsPosPot A Om)
    (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) :
    ∃ c : ℝ, 0 < c ∧ PshOff A (bdry s) (Om + LocPot.ofFun fun x => -c * r x) := by
  obtain ⟨C, hC, -, hpsh⟩ := TailBoundAlt.exists_psh_chern_bound A Om L hO hP hL
  refine ⟨1 / (2 * (C + 1)), by positivity, fun j y hy h0 w => ?_⟩
  set c := 1 / (2 * (C + 1)) with hc
  set x := (A.chart j).symm y with hx
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x := ⟨hy, L.mem_U _⟩
  have hm' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Om.U x := ⟨hy, Om.mem_U _⟩
  have c1 := (contDiffAt_pot hO x j hm').of_le two_le_infty
  have c2 := (contDiffAt_pot hL x j hm).of_le two_le_infty
  have c3 := (contDiffAt_log_norm (hS.1 x j y hm) h0).of_le two_le_infty
  have e1 : (Om + LocPot.ofFun fun x => -c * r x).φ x ∘ (A.chart j).symm =ᶠ[𝓝 y] fun z =>
      ((Om.φ x ∘ (A.chart j).symm) z + (-2 * c) * (L.φ x ∘ (A.chart j).symm) z +
        (2 * c) * Real.log ‖(s x ∘ (A.chart j).symm) z‖) - c * Real.exp 1 := by
    filter_upwards [local_eventuallyEq hS hr j hy h0] with z hz
    show Om.φ x _ + -c * r _ = _
    rw [hz]
    simp only [Function.comp_apply]
    ring
  have h1 := hpsh x j y ⟨hy, Om.mem_U _, L.mem_U _⟩ w
  have h2 := TailBoundAlt.isPsh_of_isPosPot A Om hP x j y hm' w
  have e2 := TailChernBound.levi_lin C (-1) c1 c2 w
  have h3 : 0 ≤ C * levi (Om.φ x ∘ (A.chart j).symm) y w + (-1) * levi (L.φ x ∘ (A.chart j).symm) y w :=
    e2 ▸ h1
  rw [leviAt, ← hx, levi_congr e1, levi_sub_const, levi_add_smul _ (c1.add (contDiffAt_const.mul c2)) c3,
    levi_add_smul _ c1 c2, levi_log_norm (hS.1 x j y hm) h0]
  generalize levi (Om.φ x ∘ (A.chart j).symm) y w = a at *
  generalize levi (L.φ x ∘ (A.chart j).symm) y w = b at *
  have e3 : a + -2 * c * b + 2 * c * 0 = (a + (C * a + -1 * b)) / (C + 1) := by
    rw [hc]
    field_simp
    ring
  rw [e3]
  positivity

end BdSec

theorem isBd_of_isBdSec (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om L : LocPot X) (s : X → X → ℂ)
    (hO : IsPotential A Om) (hP : IsPosPot A Om) (h : IsBdSec A Z r L s) : IsBd A Z r Om := by
  have he := IsBdSec.exp_le A Z r h
  obtain ⟨hL, hS, -, rfl, hne, hr⟩ := h
  have hi := BdSec.interior_bdry hS hne
  exact ⟨isClosed_bdry hS, BdSec.bdry_null_chart hS hi, hO, hP, BdSec.smoothOn hL hS hr, he, BdSec.toBot hL hS hr,
    BdSec.mIntegrable hL hS hr hi fun _ => hO, BdSec.exists_pshOff hO hP hL hS hr⟩

end GlobalTheory.Mean4O
