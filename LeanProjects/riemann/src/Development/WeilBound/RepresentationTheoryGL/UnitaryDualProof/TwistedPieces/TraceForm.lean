import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ContinuousCj

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def FibVan (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (F : Set (Matrix (Fin n) (Fin n) k)) : Prop :=
  ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (F ×ˢ Set.univ) → Inv Z ξ → Kills ξ {p | p.2 ≠ 0}

def NB (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k) := {x | x ∈ Bz Z ∧ IsNilpotent x}

def IsPieces (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (χ : k[X]) {m : ℕ} (F : Fin m → Set (Matrix (Fin n) (Fin n) k)) : Prop :=
  (∀ i, IsClosed (F i) ∧ F i ⊆ Bz Z ∧ ∀ g ∈ Gz Z, ∀ x ∈ F i, g.val * x * g⁻¹.val ∈ F i) ∧
    (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ ∀ x ∈ Bz Z, x.charpoly = χ → ∃ i, x ∈ F i

variable (k)

def TraceForm : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∃ τ : Matrix (Fin n) (Fin n) k →ₗ[k] k,
    (∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)) ∧ (∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0) ∧
      ∀ x ∈ NB Z, τ x = 0

def Desc : Prop :=
  ∃ μ : ∀ n : ℕ, Subalgebra k (Matrix (Fin n) (Fin n) k) → ℕ,
    ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ χ : k[X],
      ∃ (m : ℕ) (F : Fin m → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i,
        (∃ c ∈ Z, ∀ x ∈ F i, IsNilpotent (x - c)) ∨
        ((∀ (n' : ℕ) (Z' : Subalgebra k (Matrix (Fin n') (Fin n') k)), CR Z' → μ n' Z' < μ n Z → Van Z') → FibVan Z (F i))

def LocOff : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    (∀ χ : k[X], ∃ (m : ℕ) (F : Fin m → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i,
      (∃ c ∈ Z, ∀ x ∈ F i, IsNilpotent (x - c)) ∨ FibVan Z (F i)) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → ∀ U : Set (Sp k n), IsOpen U →
      (∀ p ∈ U, p.2 ≠ 0 ∧ p.1 ∉ ZN Z ∩ Bz Z) → Kills ξ U

def LocAll : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    (∀ χ : k[X], ∃ (m : ℕ) (F : Fin m → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i, FibVan Z (F i)) → Van Z

def Transl : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → FibVan Z (NB Z) → ∀ c ∈ Z,
    ∀ F : Set (Matrix (Fin n) (Fin n) k), F ⊆ Bz Z → (∀ x ∈ F, IsNilpotent (x - c)) → FibVan Z F

def NilCore : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    (∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → ∀ U : Set (Sp k n), IsOpen U →
      (∀ p ∈ U, p.2 ≠ 0 ∧ p.1 ∉ ZN Z ∩ Bz Z) → Kills ξ U) → FibVan Z (NB Z)

end PositivityTheory.RgUd.TP
