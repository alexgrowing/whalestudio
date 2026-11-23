import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRedU

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem redU_of_norm (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : RedU σ J ψ v Λ a Y :=
  redU_of σ J ψ v Λ (Orb.unitV_of σ J ψ v Λ hN hUN) hR a Y

theorem countU_of_res (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : CountU σ J ψ v Λ a Y :=
  countU_of_redU σ J ψ v Λ a Y (redU_of_norm σ J ψ v Λ hN hUN hR a Y)

end PI.OmLocU.Red
