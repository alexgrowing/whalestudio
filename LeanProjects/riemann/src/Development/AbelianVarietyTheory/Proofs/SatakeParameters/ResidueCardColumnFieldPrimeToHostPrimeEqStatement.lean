import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCardColumnFieldPrimeToHostPrimeEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueCard_columnFieldPrimeToHostPrime_eq : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (s : Formalism.L2.Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)), Formalism.L2.Col.qOf (GlobalTheory.TwU.seamP s P) = Formalism.L2.Col.qOf P := by
  first | exact @GlobalTheory.qOf_seamP | exact GlobalTheory.qOf_seamP | (intros; apply GlobalTheory.qOf_seamP <;> assumption)
