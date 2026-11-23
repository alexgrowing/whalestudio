import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicDeterminantMultiplicative
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_determinant_multiplicative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {V : HSpace E} (Φ : WittFrame V) (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R] (u : SV (wittIndex V)) (g g' : HA R hc.sig V.gram), g ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u) → g' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u) → detU Φ hc R u (g * g') = detU Φ hc R u g * detU Φ hc R u g' := by
  first | exact @GlobalTheory.LeviShift.detU_mul | exact GlobalTheory.LeviShift.detU_mul | (intros; apply GlobalTheory.LeviShift.detU_mul <;> assumption)
