import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialMinusSmallMultiplePsh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogNormPositiveStatement

namespace GlobalTheory.FubiniStudyPot

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open scoped ContDiff LinearAlgebra.Projectivization

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]

theorem smoothOn_halfLogNormSq (B : FinHolAtlas n Y) {N : ℕ} {W : Set Y} (G : Y → Fin N → ℂ)
    (hG : ∀ i, B.HoloOn W fun y => G y i) (h0 : ∀ y ∈ W, G y ≠ 0) :
    B.SmoothOn W (fun y => (1 / 2 : ℝ) * Real.log (∑ i, ‖G y i‖ ^ 2)) := by
  intro j u hu
  apply ContDiffAt.contDiffWithinAt
  have hc : ∀ i, ContDiffAt ℝ ∞ (fun v => G ((B.chart j).symm v) i) u := fun i =>
    ((hG i j u hu).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hs : ContDiffAt ℝ ∞ (fun v => ∑ i, ‖G ((B.chart j).symm v) i‖ ^ 2) u :=
    ContDiffAt.sum fun i _ => ((contDiff_norm_sq ℝ).contDiffAt).comp u (hc i)
  have hpos : 0 < ∑ i, ‖G ((B.chart j).symm u) i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (h0 _ hu.2)
    exact Finset.sum_pos' (fun k _ => by positivity)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 (by simpa using hi)) 2⟩
  exact contDiffAt_const.mul (hs.log hpos.ne')

theorem exists_smul_eq {N : ℕ} (F : Y → ℙ ℂ (Fin (N + 1) → ℂ)) {W W' : Set Y}
    (G G' : Y → Fin (N + 1) → ℂ)
    (hr : ∀ y ∈ W, ∃ h : G y ≠ 0, F y = Projectivization.mk ℂ (G y) h)
    (hr' : ∀ y ∈ W', ∃ h : G' y ≠ 0, F y = Projectivization.mk ℂ (G' y) h)
    {z : Y} (hz : z ∈ W ∩ W') : ∃ c : ℂ, c ≠ 0 ∧ G z = c • G' z := by
  obtain ⟨h1, e1⟩ := hr z hz.1
  obtain ⟨h2, e2⟩ := hr' z hz.2
  have e := e1.symm.trans e2
  rw [Projectivization.mk_eq_mk_iff'] at e
  obtain ⟨c, hc⟩ := e
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  exact h1 (by rw [← hc, zero_smul])

theorem overlap (B : FinHolAtlas n Y) {N : ℕ} (F : Y → ℙ ℂ (Fin (N + 1) → ℂ)) {W W' : Set Y}
    (hW : IsOpen W) (hW' : IsOpen W') (G G' : Y → Fin (N + 1) → ℂ)
    (hG : ∀ i, B.HoloOn W fun y => G y i) (hG' : ∀ i, B.HoloOn W' fun y => G' y i)
    (hr : ∀ y ∈ W, ∃ h : G y ≠ 0, F y = Projectivization.mk ℂ (G y) h)
    (hr' : ∀ y ∈ W', ∃ h : G' y ≠ 0, F y = Projectivization.mk ℂ (G' y) h)
    (y : Y) (hy : y ∈ W ∩ W') :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∃ H : Y → ℂ, B.HoloOn V H ∧ ∀ z ∈ V ∩ W ∩ W',
      (1 / 2 : ℝ) * Real.log (∑ i, ‖G z i‖ ^ 2) - (1 / 2 : ℝ) * Real.log (∑ i, ‖G' z i‖ ^ 2) =
        (H z).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hr' y hy.2).1
  simp only [Pi.zero_apply] at hi
  set a : Y → ℂ := fun z => G z i / G' z i with ha_def
  have ha : ∀ z ∈ W ∩ W', G' z i ≠ 0 → a z ≠ 0 ∧ G z = a z • G' z := by
    intro z hz hz0
    obtain ⟨c, hc0, hc⟩ := exists_smul_eq F G G' hr hr' hz
    have hci : G z i = c * G' z i := by rw [hc]; rfl
    have : a z = c := by simp only [ha_def]; rw [hci, mul_div_assoc, div_self hz0, mul_one]
    exact ⟨this ▸ hc0, this ▸ hc⟩
  have hlog : ∀ z ∈ W ∩ W', G' z i ≠ 0 →
      (1 / 2 : ℝ) * Real.log (∑ k, ‖G z k‖ ^ 2) - (1 / 2 : ℝ) * Real.log (∑ k, ‖G' z k‖ ^ 2) =
        Real.log ‖a z‖ := by
    intro z hz hz0
    obtain ⟨ha0, hGz⟩ := ha z hz hz0
    have hS : 0 < ∑ k, ‖G' z k‖ ^ 2 :=
      Finset.sum_pos' (fun k _ => by positivity)
        ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hz0) 2⟩
    have hsum : ∑ k, ‖G z k‖ ^ 2 = ‖a z‖ ^ 2 * ∑ k, ‖G' z k‖ ^ 2 := by
      rw [hGz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    have hn : ‖a z‖ ≠ 0 := norm_ne_zero_iff.2 ha0
    rw [hsum, Real.log_mul (pow_ne_zero 2 hn) hS.ne', Real.log_pow]
    push_cast
    ring
  have hay : a y ≠ 0 := (ha y hy hi).1
  refine ⟨{z | z ∈ W ∩ W' ∧ G' z i ≠ 0 ∧ a z / a y ∈ Complex.slitPlane}, ?_, ?_,
    fun z => Complex.log (a z / a y) + (Real.log ‖a y‖ : ℂ), ?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro z ⟨hz, hz0, hzs⟩
    have hg := ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.continuousAt_of_holoOn B (hG i) hz.1
    have hg' := ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.continuousAt_of_holoOn B (hG' i) hz.2
    have hac : ContinuousAt (fun z => a z / a y) z := (hg.div hg' hz0).div_const _
    filter_upwards [(hW.inter hW').mem_nhds hz, hg'.eventually_ne hz0,
      hac.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hzs)] with v hv1 hv2 hv3
    exact ⟨hv1, hv2, hv3⟩
  · exact ⟨hy, hi, by rw [div_self hay]; exact Complex.one_mem_slitPlane⟩
  · intro j u hu
    obtain ⟨hut, ⟨hv, hv0, hvs⟩⟩ := hu
    have hg : AnalyticAt ℂ (fun u => G ((B.chart j).symm u) i) u := hG i j u ⟨hut, hv.1⟩
    have hg' : AnalyticAt ℂ (fun u => G' ((B.chart j).symm u) i) u := hG' i j u ⟨hut, hv.2⟩
    exact (((hg.div hg' hv0).div analyticAt_const hay).clog hvs).add analyticAt_const
  · rintro z ⟨⟨⟨hz, hz0, -⟩, -⟩, -⟩
    rw [hlog z hz hz0, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div (a z) (a y),
      Real.log_div (norm_ne_zero_iff.2 (ha z hz hz0).1) (norm_ne_zero_iff.2 hay)]
    ring

def fsPot {N : ℕ} (W : Y → Set Y) (hWo : ∀ x, IsOpen (W x)) (hxW : ∀ x, x ∈ W x)
    (G : Y → Y → Fin N → ℂ) : LocPot Y where
  U := W
  isOpen_U := hWo
  mem_U := hxW
  φ x y := (1 / 2 : ℝ) * Real.log (∑ i, ‖G x y i‖ ^ 2)

theorem exists_posPot : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (B : FinHolAtlas n Y),
    IsProjective B → ∃ Om : LocPot Y, IsPotential B Om ∧ IsPosPot B Om := by
  intro n Y _ B hB
  obtain ⟨N, F, -, hloc⟩ := hB
  choose W hWo hxW G hG hr himm using hloc
  have hpot : IsPotential B (fsPot W hWo hxW G) :=
    ⟨fun x => smoothOn_halfLogNormSq B (G x) (hG x) (fun y hy => (hr x y hy).1),
      fun x x' y hy => overlap B F (hWo x) (hWo x') (G x) (G x') (hG x) (hG x') (hr x) (hr x') y hy⟩
  refine ⟨fsPot W hWo hxW G, hpot, ?_⟩
  intro x j u hu w hw
  rw [GlobalTheory.PosDom.levi_base_change B _ hpot x ((B.chart j).symm u) j u hu.1 hu.2
    (hxW ((B.chart j).symm u)) w]
  set q := (B.chart j).symm u with hq
  have hqs : q ∈ (B.chart j).source := (B.chart j).map_target hu.1
  have hcq : B.chart j q = u := (B.chart j).right_inv hu.1
  have key := GlobalTheory.T.levi_form_log_norm_positive n (N + 1) (G q ∘ (B.chart j).symm) u
    (fun i => hG q i j u ⟨hu.1, hxW q⟩) (hr q q (hxW q)).1 w (fun hmem => hw
      (himm q j hqs w (by rw [hcq]; exact hmem)))
  exact key

end

end GlobalTheory.FubiniStudyPot
