import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrTheta

def lagrInt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m nS nT : ℕ}
    (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) (C : Matrix (Fin m) (Fin nT) (AF F ⊗[F] E))
    (f : Matrix (Fin m) (Fin nS) (AF F ⊗[F] E) → ℂ) : ℂ :=
  ∫ u in 𝓕, f (C * u) ∂ν

end GlobalTheory.LagrTheta

end
