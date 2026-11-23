import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRes

noncomputable section

namespace PI.OmLocU.UnitaryOrbitCounting

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem orbAll_of_res (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.OrbAll σ J ψ v Λ a Y :=
  PI.OmLocU.Orb.orbAll_of_norm σ J ψ v Λ a Y (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN

theorem countU_of_res' (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.CountU σ J ψ v Λ a Y :=
  PI.OmLocU.Red.countU_of_res σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN hRes a Y

end PI.OmLocU.UnitaryOrbitCounting
