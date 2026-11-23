import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.AdelicCovolumeFinite
import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge

namespace CompanionTheory.SWFin

open HeckeCharacterZeroLocus.SiegelWeilU

theorem finVol (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) : FinVol F E σ M J :=
  finVol_of (fun _ _ _ _ _ _ _ _ _ _ _ h => adelicCovolumeFinite h _) F E σ hσ M J hJ

def SiegelFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      SiegelDensities F E σ M J

end CompanionTheory.SWFin
