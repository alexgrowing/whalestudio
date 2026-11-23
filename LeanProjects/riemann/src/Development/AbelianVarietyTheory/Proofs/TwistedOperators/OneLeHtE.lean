import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne

noncomputable section

namespace GlobalTheory.RatCount

open NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped TensorProduct
open scoped NNReal

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

open Classical in

def htE (x : E) : ℝ≥0 :=
  (∏ w : InfinitePlace F, max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊)) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x))

end GlobalTheory.RatCount
