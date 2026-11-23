import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedMetricAtAllRadii
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_metric_at_all_radii : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (T : Tw s.T.Z) (x x' : ToroidalCompactificationData s), (∀ σ y, x'.r σ y = x.r σ (T.pt y)) → (∀ σ y, T.MetAt y (x.eigMet σ) (x'.eigMet σ)) → (∀ σ y, ¬ LiesIn y (genBd s.T.Z) → T.MetAt y (x.hodge σ) (x'.hodge σ)) → ∀ σ (R : Option ℝ) y, T.MetAt y (x.eigMetAt σ R) (x'.eigMetAt σ R) := by
  first | exact @GlobalTheory.ShFam.GalCarry.metAt_eigMetAt | exact GlobalTheory.ShFam.GalCarry.metAt_eigMetAt | (intros; apply GlobalTheory.ShFam.GalCarry.metAt_eigMetAt <;> assumption)
