import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotMassEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff

namespace ProjPotMassEq

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPotential_congr (A : FinHolAtlas e X) {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · rw [← hU x]
    exact (hP.1 x j).congr fun t ht => (hφ x _ ht.2).symm
  · rw [← hU x, ← hU x'] at hy
    obtain ⟨W, hW, hyW, G, hG, hd⟩ := hP.2 x x' y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    rw [← hU x, ← hU x'] at hz
    rw [← hφ x z hz.1.2, ← hφ x' z hz.2, hd z hz]

theorem mInt_congr (A : FinHolAtlas e X) (Φ Φ' : Fin e → LocPot X) (g : X → ℝ)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, g ((A.chart j).symm y) ≠ 0 →
      locDens A Φ j y = locDens A Φ' j y) : mInt A Φ g = mInt A Φ' g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ =>
      setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    by_cases hg : g ((A.chart j).symm y) = 0
    · simp [hg]
    · rw [h j y hy hg]
  · rfl

theorem locDens_congr_germ (A : FinHolAtlas e X) (P Q : LocPot X) (j : Fin A.n) (y : Fin e → ℂ)
    (h : (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    locDens A (fun _ => P) j y = locDens A (fun _ => Q) j y :=
  ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun _ => h

theorem eventually_symm_mem (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {S : Set X} (hS : IsOpen S) (hyS : (A.chart j).symm y ∈ S) :
    ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ S :=
  ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hS.mem_nhds hyS)

theorem smooth_indicator (A : FinHolAtlas e X) {C : Set X} (hC : IsClopen C) {u : X → ℝ}
    (hu : A.Smooth u) : A.Smooth (C.indicator u) := by
  intro j t ht
  have hto : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 t := by
    simpa using (A.chart j).open_target.mem_nhds ht.1
  by_cases htC : (A.chart j).symm t ∈ C
  · refine (((hu j).contDiffAt hto).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_symm_mem A j ht.1 hC.isOpen htC] with t' ht'
    simp [Set.indicator_of_mem ht']
  · refine ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_symm_mem A j ht.1 hC.compl.isOpen htC] with t' ht'
    simp [Set.indicator_of_notMem ht']

theorem massIndep_clopen [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) {Φ : LocPot X}
    (hΦ : IsPotential A Φ) (Θ : LocPot X) (u : X → ℝ) (hu : A.Smooth u) {C : Set X}
    (hC : IsClopen C)
    (hΘ : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ C →
      locDens A (fun _ => Θ) j y = locDens A (fun _ => Φ + LocPot.ofFun u) j y) :
    mInt A (fun _ => Φ) (C.indicator fun _ => (1 : ℝ)) =
      mInt A (fun _ => Θ) (C.indicator fun _ => (1 : ℝ)) := by
  set w := C.indicator u with hw_def
  have hw : A.Smooth w := smooth_indicator A hC hu
  have hΦw : IsPotential A (Φ + LocPot.ofFun w) := isPotentialAdd A _ _ hΦ (isPotential_ofFun A w hw)
  have hg : Continuous (C.indicator fun _ : X => (1 : ℝ)) := hC.continuous_indicator continuous_const
  have hg' : Continuous (Cᶜ.indicator fun _ : X => (1 : ℝ)) :=
    hC.compl.continuous_indicator continuous_const
  have hsplit : (fun _ : X => (1 : ℝ)) = fun x =>
      1 * C.indicator (fun _ => (1 : ℝ)) x + Cᶜ.indicator (fun _ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ C
    · simp [hx]
    · simp [hx]
  have h1 := mIntLinear A (fun _ => Φ) (fun _ => hΦ) 1 _ _
    (mIntegrableCont A _ (fun _ => hΦ) _ hg) (mIntegrableCont A _ (fun _ => hΦ) _ hg')
  have h2 := mIntLinear A (fun _ => Φ + LocPot.ofFun w) (fun _ => hΦw) 1 _ _
    (mIntegrableCont A _ (fun _ => hΦw) _ hg) (mIntegrableCont A _ (fun _ => hΦw) _ hg')
  rw [← hsplit] at h1 h2
  have h3 : mInt A (fun _ => Φ + LocPot.ofFun w) (fun _ => 1) = mInt A (fun _ => Φ) (fun _ => 1) :=
    massIndep A (fun _ => Φ) (fun _ => w) (fun _ => hΦ) (fun _ => hw)
  have h4 : mInt A (fun _ => Φ + LocPot.ofFun w) (Cᶜ.indicator fun _ => (1 : ℝ)) =
      mInt A (fun _ => Φ) (Cᶜ.indicator fun _ => (1 : ℝ)) := by
    refine mInt_congr A _ _ _ fun j y hy hne => locDens_congr_germ A _ _ j y ?_
    have hyC : (A.chart j).symm y ∈ Cᶜ := by
      by_contra h
      exact hne (Set.indicator_of_notMem h _)
    filter_upwards [eventually_symm_mem A j hy hC.compl.isOpen hyC] with y' hy'
    show Φ.φ _ _ + w _ = Φ.φ _ _
    rw [hw_def, Set.indicator_of_notMem hy', add_zero]
  have h5 : mInt A (fun _ => Φ + LocPot.ofFun w) (C.indicator fun _ => (1 : ℝ)) =
      mInt A (fun _ => Θ) (C.indicator fun _ => (1 : ℝ)) := by
    refine mInt_congr A _ _ _ fun j y hy hne => ?_
    have hyC : (A.chart j).symm y ∈ C := by
      by_contra h
      exact hne (Set.indicator_of_notMem h _)
    rw [hΘ j y hy hyC]
    refine locDens_congr_germ A _ _ j y ?_
    filter_upwards [eventually_symm_mem A j hy hC.isOpen hyC] with y' hy'
    show Φ.φ _ _ + w _ = Φ.φ _ _ + u _
    rw [hw_def, Set.indicator_of_mem hy']
  linarith

end General

end ProjPotMassEq

end GroundTheory.Heights₂.Heights.Targets
