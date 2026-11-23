import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHodgeMetricOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_hodge_metric_off_boundary : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (T : Tw s.T.Z) (x x' : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (y : GlobalTheory.CxPts (genStr s.T.Z) σ), ¬ LiesIn y (genBd s.T.Z) → T.MetAt y (x.hodge σ) (x'.hodge σ) := by
  first | exact @GlobalTheory.ShFam.GalCarry.hodge_metAt | exact GlobalTheory.ShFam.GalCarry.hodge_metAt | (intros; apply GlobalTheory.ShFam.GalCarry.hodge_metAt <;> assumption)
