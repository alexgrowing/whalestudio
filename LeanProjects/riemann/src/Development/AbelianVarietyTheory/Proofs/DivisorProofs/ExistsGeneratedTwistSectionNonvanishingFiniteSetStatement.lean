import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratedTwistSectionNonvanishingFiniteSet
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
theorem _root_.GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  first | exact @GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | exact GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | (intros; apply GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero <;> assumption)
