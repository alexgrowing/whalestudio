import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

open HolomorphicMinorCharts in
theorem r_holmap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e e' : ℕ) (X Y : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) (V : Y → Set Y) (mu : Y → Y → (Σ k, ι k) → ℂ), IsEmbedded A P U lam → (∀ y, IsOpen (V y) ∧ y ∈ V y) → (∀ y p, B.HoloOn (V y) fun y' => mu y y' p) → (∀ y, ∀ y' ∈ V y, mu y y' ∈ mcPts P) → (∀ y y', ∀ w ∈ V y ∩ V y', SameOrbit (mu y w) (mu y' w)) → ∃ π : Y → X, HoloMap B A π ∧ ∀ y, SameOrbit (lam (π y) (π y)) (mu y y) := by
  intro K _ ι _ P e e' X Y _ _ _ _ A B U lam V mu hE hV hm hmem hc
  choose π hπ using fun y => hE.surj (mu y y) (hmem y y (hV y).2)
  have hcl := isClosed_minors (U := U) (lam := lam) (V := V) (mu := mu) (fun x => ⟨hE.isOpen x, hE.mem_U x⟩)
    (fun x p => holo_continuousAt (hE.holo x p) (hE.mem_U x)) hE.compat hV
    (fun y p => holo_continuousAt (hm y p) (hV y).2) hc
  have hcont : ∀ y, ContinuousAt π y := fun y =>
    continuousAt_of_closed_rel hcl (fun y => minors_of_so (hπ y)) fun x hx =>
      hE.inj _ _ (so_trans (so_of_minors hx (hE.mem x x (hE.mem_U x)).1 (hmem y y (hV y).2).1) (so_symm (hπ y)))
  refine ⟨π, ⟨continuous_iff_continuousAt.mpr hcont, fun j k w hw => ?_⟩, hπ⟩
  set y := (B.chart j).symm w with hy
  have h := analyticAt_factor (A := A) (B := B) (U := U (π y)) (lam := lam (π y)) (V := V y) (mu := mu y) (π := π)
    (y := y) (hE.holo _) (hE.mem_U _) (hm y) (hV y).2 (hcont y) (hE.mem _ _ (hE.mem_U _)).1 (hE.immersion (π y))
    (by
      filter_upwards [(hV y).1.mem_nhds (hV y).2, hcont y ((hE.isOpen _).mem_nhds (hE.mem_U (π y)))] with w' h1 h2
      exact so_trans (hE.compat _ _ _ ⟨h2, hE.mem_U _⟩) (so_trans (hπ w') (hc _ _ _ ⟨(hV _).2, h1⟩)))
    j k ((B.chart j).map_target hw.1) hw.2
  rwa [hy, (B.chart j).right_inv hw.1] at h

end PositivityTheory.UnitarySelfGeneration
