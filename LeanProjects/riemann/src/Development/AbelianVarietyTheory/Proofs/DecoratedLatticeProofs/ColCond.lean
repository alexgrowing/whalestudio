import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.PhiOneVal

def ColCond {E : Type} [Field E] [NumberField E] {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E)
    (x : (Fin a → E) →ₗ[E] (Fin b → E)) : Prop :=
  ∀ r : Fin a, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E,
    (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * x (Pi.single r 1) q) ∧
    ∀ q : Fin b, q.1 + 1 = b → t * (c q - if r.1 + 1 = a then s else 0) ∈ P.asIdeal

end GlobalTheory.PhiOneVal
