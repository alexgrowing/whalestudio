import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnPrimeToBasePrimePreservesCommonPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPrimeToBasePrime_preserves_common_place : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok → ∀ P Q : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = Q.under (𝓞 X.F) → (seamP s P).under (𝓞 D.host.F) = (seamP s Q).under (𝓞 D.host.F) := by
  first | exact @GlobalTheory.TwU.seamP_under_eq | exact GlobalTheory.TwU.seamP_under_eq | (intros; apply GlobalTheory.TwU.seamP_under_eq <;> assumption)
