import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open Filter Topology

namespace GlobalTheory.Div.SmoothLimsup

theorem continuousAt_of_smoothOn {D : ℕ} {Y : Type} [TopologicalSpace Y]
    (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (S : Set Y) (u : Y → ℝ) (hS : IsOpen S)
    (hu : A.SmoothOn S u) {y : Y} (hy : y ∈ S) : ContinuousAt u y := by
  obtain ⟨j, hj⟩ := A.cover y
  set c := A.chart j
  have hT : IsOpen (c.target ∩ c.symm ⁻¹' S) := c.isOpen_inter_preimage_symm hS
  have hmem : c y ∈ c.target ∩ c.symm ⁻¹' S := ⟨c.map_source hj, by simpa [c.left_inv hj] using hy⟩
  have h1 : ContinuousAt (u ∘ c.symm) (c y) :=
    ((hu j).continuousOn).continuousAt (hT.mem_nhds hmem)
  have h2 : ContinuousAt c y := c.continuousAt hj
  have h3 : ContinuousAt ((u ∘ c.symm) ∘ c) y := h1.comp h2
  refine h3.congr ?_
  filter_upwards [c.open_source.mem_nhds hj] with x hx
  simp [c.left_inv hx]

theorem main : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (S : Set Y) (u : Y → ℝ), IsOpen S → A.SmoothOn S u → ContinuousOn u S ∧ ∀ y ∈ S, GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt S u y = u y := by
  intro D Y _ A S u hS hu
  refine ⟨fun y hy => (continuousAt_of_smoothOn A S u hS hu hy).continuousWithinAt, ?_⟩
  intro y hy
  unfold GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt
  rw [nhdsWithin_eq_nhds.mpr (hS.mem_nhds hy)]
  exact ((continuous_coe_real_ereal.tendsto (u y)).comp
    (continuousAt_of_smoothOn A S u hS hu hy)).limsup_eq

end GlobalTheory.Div.SmoothLimsup
