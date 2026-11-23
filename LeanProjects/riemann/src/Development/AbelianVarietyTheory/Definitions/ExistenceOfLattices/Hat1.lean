import Mathlib

noncomputable section

namespace GlobalTheory.AdLat

open NumberField IsDedekindDomain
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

abbrev RA : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

variable {E}

def fv {n : ℕ} (v : Fin n → E) : Fin n → RA F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

def hat {n : ℕ} (L : Set (Fin n → E)) : AddSubgroup (Fin n → RA F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L, z = fun i => a ⊗ₜ x i}

def hat1 (J : Set E) : AddSubgroup (RA F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ J, z = a ⊗ₜ x}

def latOf {n : ℕ} (g : Matrix (Fin n) (Fin n) (RA F E)) (L : Set (Fin n → E)) : Set (Fin n → E) :=
  {v | fv F v ∈ g.mulVec '' (hat F L : Set (Fin n → RA F E))}

variable {F}

def sg (A : Type) [CommRing A] [Algebra F A] (c : E ≃ₐ[F] E) : A ⊗[F] E →ₐ[F] A ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id F A) (c : E →ₐ[F] E)

def hermA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) : RA F E :=
  ∑ a, ∑ b, x a * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G a b) * sg (FiniteAdeleRing (𝓞 F) F) c (y b)

end GlobalTheory.AdLat
