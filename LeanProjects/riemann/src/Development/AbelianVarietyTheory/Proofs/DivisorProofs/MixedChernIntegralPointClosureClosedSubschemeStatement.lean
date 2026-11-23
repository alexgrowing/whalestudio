import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubscheme
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ [IsIntegral Y] (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (CycIntg L f (π (genericPoint Y)) ↔ Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y))) ∧ cycInt L f (π (genericPoint Y)) = Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) := by
  first | exact @GlobalTheory.Mix.cycInt_of_closedImmersion | exact GlobalTheory.Mix.cycInt_of_closedImmersion | (intros; apply GlobalTheory.Mix.cycInt_of_closedImmersion <;> assumption)
