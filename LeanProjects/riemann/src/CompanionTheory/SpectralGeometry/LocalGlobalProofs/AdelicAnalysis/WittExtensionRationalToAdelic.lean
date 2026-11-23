import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicOrbitOfRationalTupleStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransA

theorem trans_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
    ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y :=
  fun F E _ _ _ _ _ σ hcm M J hJ n =>
    GlobalTheory.T.adelic_orbit_of_rational_tuple F E σ hcm (AF F) (PIW.AdelicOrbitU.stP F) n M J hJ

end GlobalTheory.CompanionTheory.SW.TransA
