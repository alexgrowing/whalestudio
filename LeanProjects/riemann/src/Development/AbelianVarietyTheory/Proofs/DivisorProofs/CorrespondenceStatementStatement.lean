import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.correspondence_statement : CorrSt := by
  first | exact @GlobalTheory.ShFam.GalCarry.corrSt | exact GlobalTheory.ShFam.GalCarry.corrSt | (intros; apply GlobalTheory.ShFam.GalCarry.corrSt <;> assumption)
