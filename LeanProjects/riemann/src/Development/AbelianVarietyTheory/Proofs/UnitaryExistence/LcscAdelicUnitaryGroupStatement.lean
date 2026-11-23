import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lcsc_adelic_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  first | exact @GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | exact GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | (intros; apply GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary <;> assumption)
