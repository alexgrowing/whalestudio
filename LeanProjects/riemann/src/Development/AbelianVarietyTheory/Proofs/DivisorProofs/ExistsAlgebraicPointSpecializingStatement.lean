import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_point_specializing : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime → ∀ (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens), ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), resP v = p ∧ below y.1 ∈ W ∧ z ≫ V.π = y.1 ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ U ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) := by
  first | exact @GlobalTheory.Mean4O.Cover.ThroughFibre.exists_algPt_through | exact GlobalTheory.Mean4O.Cover.ThroughFibre.exists_algPt_through | (intros; apply GlobalTheory.Mean4O.Cover.ThroughFibre.exists_algPt_through <;> assumption)
