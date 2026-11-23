import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Split : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (F : Fin m → Set (Matrix (Fin n) (Fin n) k)),
    (∀ i, IsClosed (F i) ∧ ∀ g ∈ Gz Z, ∀ x ∈ F i, g.val * x * g⁻¹.val ∈ F i) → (∀ i j, i ≠ j → Disjoint (F i) (F j)) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((⋃ i, F i) ×ˢ Set.univ) → Inv Z ξ →
      ∃ η : Fin m → (Sp k n → ℂ) →ₗ[ℂ] ℂ, (∀ i, Supp (η i) (F i ×ˢ Set.univ) ∧ Inv Z (η i)) ∧
        ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ f = ∑ i, η i f

def LocChi : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (U : Set (Sp k n)), IsOpen U →
    (∀ χ : k[X], ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((Bz Z ∩ {x | x.charpoly = χ}) ×ˢ Set.univ) → Inv Z ξ → Kills ξ U) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Kills ξ U

end PositivityTheory.RgUd.TP.Loc
