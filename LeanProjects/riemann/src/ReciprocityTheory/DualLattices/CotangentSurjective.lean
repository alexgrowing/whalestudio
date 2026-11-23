import ReciprocityTheory.DualLattices.TensorSpan
import ReciprocityTheory.DualLattices.SmallLevelClassSet

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable (p : ℕ) [Fact p.Prime] (g : ℕ)

abbrev Ix (g : ℕ) := Fin g ⊕ Fin g

abbrev TT := Ix g → ℤ_[p]

abbrev Nb := Ix g → ZMod p

def red (t : TT p g) : Nb p g := fun i => PadicInt.toZMod (t i)

def pair (E : Matrix (Ix g) (Ix g) ℤ_[p]) (s t : TT p g) : ℤ_[p] := s ⬝ᵥ (E *ᵥ t)

def sqIdeal {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    (I : Submodule R (X → C)) : Submodule R (X → C) :=
  Submodule.span R {h | ∃ f ∈ I, ∃ f' ∈ I, h = f * f'}

abbrev LieDualModP (q : ℕ) (R : Type) [CommRing R] (n : ℕ) :=
  (Fin n → R) ⧸ (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin n → R)))

def HasLen {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (M : Type) [AddCommGroup M] [Module R M] (x : NNReal) : Prop :=
  ∃ (m : ℕ) (c : Fin m → R), Nonempty (M ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span {c i})) ∧
    ∏ i, v (algebraMap R C (c i)) = x

abbrev OmAA {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] (M : Submodule R (X → C)) :=
  augIdeal M ⧸ (sqIdeal (augIdeal M)).comap (augIdeal M).subtype

structure HodgeTateDatum {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O]
    (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) where

  ρ : O →ₐ[ℤ_[p]] Matrix (Ix g) (Ix g) ℤ_[p]

  ρL : O →+* Matrix (Fin g) (Fin g) R

  P : Matrix (Ix g) (Ix g) ℤ_[p]
  PL : Matrix (Fin g) (Fin g) R

  E : Matrix (Ix g) (Ix g) ℤ_[p]
  E_alternating : Eᵀ = -E ∧ ∀ i, E i i = 0
  isUnit_det_E : IsUnit E.det
  E_equivariant : ∀ a, (ρ a)ᵀ * E = E * ρ (σ a)
  projectors : P * P = P ∧ PL * PL = PL ∧ Pᵀ * E = E * P ∧
    (∀ a, P * ρ a = ρ a * P) ∧ ∀ a, PL * ρL a = ρL a * PL

  Ht : Matrix (Fin g) (Ix g) R

  Bt : Matrix (Fin g) (Ix g) R
  Ht_equivariant : (∀ a, Ht * (ρ a).map (algebraMap ℤ_[p] R) = (ρL (σ a))ᵀ * Ht) ∧
    Ht * P.map (algebraMap ℤ_[p] R) = PLᵀ * Ht
  form_eq_alt : Btᵀ * Ht - Htᵀ * Bt = cp • E.map (algebraMap ℤ_[p] R)

  AA : HopfOrder (C := C) R (Nb p g)
  h3 : ∀ a, ∀ f ∈ AA.carrier, ∃ f' ∈ AA.carrier, ∀ t, f' (red p g t) = f (red p g (ρ a *ᵥ t))

  h4 : ∀ k : Fin g,
    (∃ f ∈ AA.carrier, ∀ t : TT p g, ∃ r : R, algebraMap R C
      ((Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - f (red p g t) = algebraMap R C (p * r)) ∧
    (∃ f ∈ AA.carrier, ∀ t : TT p g, ∃ r : R, algebraMap R C
      ((Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - f (red p g t) = algebraMap R C (p * r))

  h5 : p = 2 → ∀ s : TT p g, ∃ f ∈ AA.carrier, ∀ t : TT p g,
    f (red p g t) = (-1 : C) ^ (PadicInt.toZMod (pair p g E s t)).val

  φ : augIdeal AA.carrier →ₗ[R] LieDualModP p R g
  cotangent_surjective : Function.Surjective φ
  cotangent_ker_eq : LinearMap.ker φ = (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype
  cotangent_linear : ∀ (a : O) (f f' : augIdeal AA.carrier) (l : Fin g → R),
    (∀ t, (f' : Nb p g → C) (red p g t) = (f : Nb p g → C) (red p g (ρ a *ᵥ t))) →
    φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk ((ρL a)ᵀ *ᵥ l)

structure HodgeTateSetting {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O]
    (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) : Prop where
  integers : v.Integers R
  p_lt : v (algebraMap R C (p : R)) < 1
  p_ne : v (algebraMap R C (p : R)) ≠ 0
  cp_val : v (algebraMap R C cp) ^ (p - 1) = v (algebraMap R C (p : R))
  invol : ∀ a, σ (σ a) = a

end ReciprocityTheory.PGsh.Up
