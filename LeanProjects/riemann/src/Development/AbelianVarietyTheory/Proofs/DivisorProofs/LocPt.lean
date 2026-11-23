import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.FinComm

variable {F : Type} [Field F] [NumberField F]

def indO {κ : Type} (v : Pl F) : (κ → Fv F v) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def locOp (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ] (p : (κ → Fv F v) × (κ → Fv F v))
    (φ : (κ → Fv F v) → ℂ) : (κ → Fv F v) → ℂ :=
  fun x => psiLoc ψ v (x ⬝ᵥ p.2 + p.1 ⬝ᵥ p.2 / 2) * φ (x + p.1)

def locPt (v : Pl F) {κ : Type} (p : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) :=
  (fun i => evFin F v (p.1 i), fun i => evFin F v (p.2 i))

end GlobalTheory.FinComm
