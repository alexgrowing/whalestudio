import Development.WeilBound.KatoCoprimality.CoprimePowers.CoprimePowerSubOne.CoprimePowSubOne
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

theorem UpperTheory.Gal.Seam.sigC_eq :
    ∀ (l : ℕ) [Fact l.Prime] (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (y : ℂ_[l]), GaloisFrobeniusFixed.σC g y = Formalism.Per.σC g y := by
  intro l _ g y
  induction y using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (GroundTheory.PAdicHodge.continuous_galCp (GaloisFrobeniusFixed.toBot g))
      (AddMonoidHomClass.isometry_of_norm (Formalism.Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  | ih a =>
    rw [GlobalTheory.RingBasics.σC_coe]
    exact GroundTheory.PAdicHodge.galCp_coe (GaloisFrobeniusFixed.toBot g) a
