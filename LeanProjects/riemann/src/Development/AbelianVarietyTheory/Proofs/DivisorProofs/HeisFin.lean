import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM

namespace GlobalTheory.FinHeis

variable (F : Type) [Field F] [NumberField F] {κ : Type}

def finA (z : Af F) : AF F := LinearMap.inr F (Ainf F) (Af F) z

def heisA [Fintype κ] (ψ : AddChar (AF F) ℂ) (a b : κ → Af F) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  fun x => ψ (x ⬝ᵥ fun i => finA F (b i)) * Φ (x + fun i => finA F (a i))

def heisFin [Fintype κ] (ψ : AddChar (AF F) ℂ) (a b : κ → Af F) (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  fun z => ψ (finA F (z ⬝ᵥ b)) * g (z + a)

def pt (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), z i)

end GlobalTheory.FinHeis

end
