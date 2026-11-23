import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SmoothContinuousAt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem r_snc : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L₀ : LocPot X) (s₀ : X → X → ℂ) (n₀ : ℕ) (m₀ : Fin n₀ → ℕ) (W₀ : Fin n₀ → Set X) (L : LocPot X) (s : X → X → ℂ), IsSNC A L₀ s₀ m₀ W₀ → IsPotential A L → IsSection A L s → bdry s ⊆ {x | s₀ x x = 0} → (∀ x x', ∀ y ∈ L₀.U x ∩ L₀.U x', (s₀ x y = 0 ↔ s₀ x' y = 0)) → ∃ (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set X), IsSNC A L s m W := by
  intro e X _ _ _ A L₀ s₀ n₀ m₀ W₀ L s h₀ hL hs hb hz
  exact CSnc.snc_of_loc hL hs (CSnc.exists_loc h₀ hs hb hz)

end PositivityTheory.UnitarySelfGeneration
