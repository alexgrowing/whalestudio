import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory.Published

def UnitaryIrreducibleAdmissible : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F))
      (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GLoc σ J v →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∀ K : Subgroup (GLoc σ J v), IsOpen (K : Set (GLoc σ J v)) → IsCompact (K : Set (GLoc σ J v)) →
          FiniteDimensional ℂ (fixed (toRep π) K)

end GlobalTheory.Published

end
