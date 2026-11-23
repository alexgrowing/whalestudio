import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PlacesOverU

noncomputable section

namespace GlobalTheory.UPel.HT

open NumberField Matrix
open scoped TensorProduct

variable {K F : Type} [Field K] [NumberField K] [IsCMField K] [Field F] [NumberField F] [IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime]

def HTDatum.realRep (D : HTDatum K F p) (ρ : (F →+* ℂ) → D.B →+* Matrix (Fin D.n) (Fin D.n) ℂ) :
    ℝ ⊗[ℚ] D.B →ₐ[ℝ] (D.Φ → Matrix (Fin D.n) (Fin D.n) ℂ) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (Pi.algHom ℚ _ fun τ => (ρ τ).toRatAlgHom)
    (fun r y => Algebra.commute_algebraMap_left r _)

end GlobalTheory.UPel.HT
