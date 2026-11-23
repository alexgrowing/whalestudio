import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def JCPoly : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ y, ∃ P : k[X], ∀ x ∈ Bz Z, pZ Z x = y →
    Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P)

def SliceVan : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ s ∈ Bz Z,
    Module.End.IsSemisimple (Matrix.toLin' s) → Van (adj Z s) →
    ∀ (F : Set (Matrix (Fin n) (Fin n) k)) (P : k[X]), IsClosed F → F ⊆ Bz Z →
      (∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F) →
      (∀ x ∈ F, aeval x P ∈ F ∧ Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P) ∧
        ∃ g ∈ Gz Z, g.val * aeval x P * g⁻¹.val = s) →
      ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (F ×ˢ Set.univ) → Inv Z ξ → Kills ξ {p | p.2 ≠ 0}

end PositivityTheory.RgUd.T.Desc
