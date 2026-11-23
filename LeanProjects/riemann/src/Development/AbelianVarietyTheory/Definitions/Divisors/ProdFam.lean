import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E : Type} [AddCommGroup E] [Module k E]

open Classical in

def idxSign (τ : κ → ι) (S : Finset κ) : ℤ := (-1) ^ ((S ×ˢ S).filter fun x => x.1 < x.2 ∧ τ x.2 < τ x.1).card

open Classical in

def pullIdx (τ : κ → ι) (a : Finset ι → E) : Finset κ → E := fun S =>
  if Set.InjOn τ (S : Set κ) then idxSign τ S • a (S.image τ) else 0

end Pull

section Cross

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

def fstL : ι ×ₗ κ → ι := fun x => (ofLex x).1

def sndL : ι ×ₗ κ → κ := fun x => (ofLex x).2

def crossC {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') :
    Finset (ι ×ₗ κ) → E'' := fun u =>
  ∑ j ∈ u, μ (pullIdx fstL a (u.filter (· ≤ j))) (pullIdx sndL b (u.filter (j ≤ ·)))

def prodFam {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (S : Finset (ι ×ₗ κ)) : Submodule k E'' :=
  Submodule.map₂ μ (A (S.image fstL)) (B (S.image sndL))

def Disjoint₂ {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') : Prop :=
  ∀ I J, Function.Injective (TensorProduct.lift (μ.compl₁₂ (A I).subtype (B J).subtype))

end Cross

end GlobalTheory.PD
