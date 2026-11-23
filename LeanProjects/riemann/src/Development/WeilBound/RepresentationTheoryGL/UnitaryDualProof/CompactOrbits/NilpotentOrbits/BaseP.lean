import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def qZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) : Fin (Module.finrank k Z) → k :=
  fun i => trace (((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) * x)

open Classical in

def piZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k :=
  if h : ∃ c ∈ Z, qZ Z c = qZ Z x then h.choose else 0

def sig (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (p : Sp k n) : Sp k n :=
  (piZ Z p.1 + (t : k) • (p.1 - piZ Z p.1), p.2)

def pull (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) :
    ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ) where
  toFun ξ := ξ ∘ₗ LinearMap.funLeft ℂ ℂ (sig Z t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dB0 (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : ℕ :=
  Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) - Module.finrank k Z

def UU : Set (Sp k n) := {p | p.2 ≠ 0}

def Fib (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (y : Fin (Module.finrank k Z) → k) : Set (Sp k n) :=
  (Bz Z ∩ qZ Z ⁻¹' {y}) ×ˢ Set.univ

def FourP : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    ∃ 𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ),
      (∀ ξ, Supp ξ (Bz Z ×ˢ Set.univ) → Supp (𝓕 ξ) (Bz Z ×ˢ Set.univ)) ∧
      (∀ ξ y, Supp ξ (Fib Z y) → Supp (𝓕 ξ) (Fib Z y)) ∧
      (∀ ξ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Inv Z (𝓕 ξ)) ∧
      (∀ ξ, Supp ξ (Bz Z ×ˢ Set.univ) → (Kills ξ UU ↔ Kills (𝓕 ξ) UU)) ∧
      (∀ ξ, (∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ f = 0) →
        ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), 𝓕 ξ f = 0) ∧
      ∀ (t : kˣ) ξ, Supp ξ (Bz Z ×ˢ Set.univ) → ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
        𝓕 (pull Z t ξ) f = ((((nabs k t)⁻¹ ^ dB0 Z : ℝ)) : ℂ) * pull Z t⁻¹ (𝓕 ξ) f

def OrbP : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → 0 < dB0 Z → ∀ t : kˣ, nabs k t < 1 → ∀ y,
    ∃ a : List ℝ, (∀ x ∈ a, 2 * x < dB0 Z) ∧ ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Fib Z y) → Inv Z ξ →
      Kills ξ (UU ∩ {p | p.1 ∉ ZN Z}) →
      Kills (((a.map fun x => pull Z t - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id).prod : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ)) ξ) UU

def LocQ : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    (∀ y (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ), Supp ξ (Fib Z y) → Inv Z ξ → Kills ξ UU) → Van Z

def BaseP : Prop := ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → dB0 Z = 0 → Van Z

end PositivityTheory.RgUd.T.Nil
