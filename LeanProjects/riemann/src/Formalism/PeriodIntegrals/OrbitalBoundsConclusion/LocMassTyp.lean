import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LocalMassTypeOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.RightInvariantCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.KUnip1Of

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain

theorem locMassTyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) : Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ :=
  PI.LocMassTypW.local_mass_type_of_parts PI.LocMassTypR.right_invariant_compact
    (PI.LocMassTypW.kUnip1_of PI.LocMassTypS.split_reduction) σ J ψ v g P P' Λ
