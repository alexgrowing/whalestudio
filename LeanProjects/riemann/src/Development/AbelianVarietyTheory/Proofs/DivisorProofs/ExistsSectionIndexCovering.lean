import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.OriginChart

theorem exists_chart_lbPow_eSec : ∀ (K'' : Type) [Field K''] (P : Out.PolAV (Sp K'')) (N : ℕ),
    ∃ i₀ : (lbPow P.L N).ι, ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ := by
  intro K'' _ P N
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum K'') := inferInstance
  have hy : (eSec P.A) y ∈ ⨆ i, P.L.U i := by rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨fun _ => i, fun w _ => ?_⟩
  rw [GlobalTheory.Cartier.lbPow_U]
  have hw : w = y := Subsingleton.elim (α := PrimeSpectrum K'') _ _
  rw [hw]
  exact hi

end GlobalTheory.OriginChart
