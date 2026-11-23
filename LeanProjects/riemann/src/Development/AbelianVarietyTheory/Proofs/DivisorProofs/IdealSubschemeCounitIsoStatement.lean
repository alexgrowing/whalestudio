import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSubschemeCounitIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_subscheme_counit_iso : ∀ {X : Scheme.{0}} (I : X.IdealSheafData) (G : I.subscheme.Modules) [G.IsQuasicoherent], IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).counit.app G) := by
  first | exact @GlobalTheory.QCoh.ClosedCounit.isIso_counit_subschemeι | exact GlobalTheory.QCoh.ClosedCounit.isIso_counit_subschemeι | (intros; apply GlobalTheory.QCoh.ClosedCounit.isIso_counit_subschemeι <;> assumption)
