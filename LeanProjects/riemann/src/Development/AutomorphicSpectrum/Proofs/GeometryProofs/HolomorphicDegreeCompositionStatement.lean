import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDegreeComposition
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degree_composition : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff | exact GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff | (intros; apply GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff <;> assumption)
