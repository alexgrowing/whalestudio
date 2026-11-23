import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

noncomputable section

namespace Formalism.L2.SG.Pf.NcLoc

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def OmLocU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → IsSDLoc σ J v Λ → UnramAt (E := E) v → a ≤ n → IsPrim v Λ Y →
  (∃ w ∈ OEv (E := E) v, (gramR (Fv F v) σ J Y).det ∈ OEv (E := E) v ∧ (gramR (Fv F v) σ J Y).det * w = 1) →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y} =
      ENNReal.ofReal (absV v (dV v) ^ ((n : ℝ) * a - (a : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (n - a + 1) n,
          (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

end Formalism.L2.SG.Pf.NcLoc
