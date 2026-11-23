import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

namespace HTChart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

structure PullsBack {A' K' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [Algebra K K']
    {Ω' : Type} [AddCommGroup Ω'] [Module K' Ω'] [Module A' Ω'] [IsScalarTower A' K' Ω']
    [Module K Ω'] [IsScalarTower K K' Ω']
    (D' : HTChart A' K' c p R N Ω') (f : A →+* A') (ψ : Ω →ₗ[K] Ω') : Prop where
  comm : ∀ a : A, algebraMap A' K' (f a) = algebraMap K K' (algebraMap A K a)
  base : IsBaseChange K' ψ
  om_eq : D'.om = Submodule.span A' (ψ '' (D.om : Set Ω))
  lin : ∀ (a : 𝓞 E) (x : Ω), ψ (D.ρΩ a x) = D'.ρΩ a (ψ x)
  e_eq : D'.e = D.e
  h_eq : ∀ x, ∃ y ∈ D'.om, D'.h x = ψ (D.h x) + (p ^ R) • y

def IsFrame (σ : E →+* K) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) {j k : ℕ}
    (bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom))))
    (bM : Basis (Fin k) A (D.omHT σ)) (g : Matrix (Fin N) (Fin j ⊕ Fin k) A) : Prop :=
  (∀ a, ∃ x' : Fin N → A, (fun l => g l (Sum.inl a)) = i (bW a) + ((p : A) ^ m) • x') ∧
  ∀ a, ∃ y ∈ D.omHT σ, D.q σ (fun l => g l (Sum.inr a)) = (bM a : Ω) + ((p : A) ^ m) • y

end HTChart

def leadMinor {B : Type} [CommRing B] {N : ℕ} (g : Matrix (Fin N) (Fin N) B) (i : ℕ) (hi : i ≤ N)
    (J : Fin i → Fin N) : B :=
  (g.submatrix J (Fin.castLE hi)).det

end GlobalTheory.CompanionTheory.Ar.HT
