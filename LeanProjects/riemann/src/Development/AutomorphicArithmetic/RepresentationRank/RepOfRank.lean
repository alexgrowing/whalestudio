import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.RepresentationRank

noncomputable abbrev proj {S : Scheme.{0}} {T G : Over S} (V : (T ⊗ G).left.Opens) :
    (V : Scheme.{0}) ⟶ T.left :=
  V.ι ≫ (fst T G).left

def Rep {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens) : Prop :=
  IsClosed (U : Set (Y ⊗ G).left) ∧
    ∀ (T : Over S) (V : (T ⊗ G).left.Opens), IsClosed (V : Set (T ⊗ G).left) →
      ∃! y : T ⟶ Y, (y ▷ G).left ⁻¹ᵁ U = V

def RepOfRank {S : Scheme.{0}} (r : ℕ) (G Y : Over S) (U : (Y ⊗ G).left.Opens) : Prop :=
  IsClosed (U : Set (Y ⊗ G).left) ∧ (∀ y, (proj U).finrank y = r) ∧
    ∀ (T : Over S) (V : (T ⊗ G).left.Opens), IsClosed (V : Set (T ⊗ G).left) →
      (∀ t, (proj V).finrank t = r) → ∃! y : T ⟶ Y, (y ▷ G).left ⁻¹ᵁ U = V

end UpperTheory.RepresentationRank
