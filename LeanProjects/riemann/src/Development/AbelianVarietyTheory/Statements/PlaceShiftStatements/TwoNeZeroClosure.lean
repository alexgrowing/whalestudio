import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.LTors

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def tv (A : AbVar K) : Tl l A →ₗ[ℤ_[l]] Vl l A := TensorProduct.mk ℤ_[l] ℚ_[l] (Tl l A) 1

def IsLPow {A : AbVar K} (G : Subgroup A.Pt) : Prop := Finite G ∧ ∃ a : ℕ, Nat.card G = l ^ a

def IsLatOver {A : AbVar K} (L : Submodule ℤ_[l] (Vl l A)) : Prop := L.FG ∧ LinearMap.range (tv l A) ≤ L

def latSet {A : AbVar K} (G : Subgroup A.Pt) : Set (Vl l A) :=
  {x | ∃ (n : ℕ) (t : Tl l A), x = (((l : ℚ_[l]) ^ n)⁻¹ ⊗ₜ[ℤ_[l]] t) ∧ t.lev n ∈ G}

def LTorsLatticeSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K),
    (∀ G : Subgroup A.Pt, IsLPow l G →
      ∃ L : Submodule ℤ_[l] (Vl l A), (L : Set (Vl l A)) = latSet l G ∧ IsLatOver l L) ∧
    (∀ L : Submodule ℤ_[l] (Vl l A), IsLatOver l L →
      ∃! G : Subgroup A.Pt, IsLPow l G ∧ (L : Set (Vl l A)) = latSet l G) ∧
    (∀ G : Subgroup A.Pt, IsLPow l G →
      (∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ (ptMap q).ker = G ∧ deg q = Nat.card G) ∧
      ∀ (B : AbVar K) (q : A ⟶ B), IsIsogeny q → (ptMap q).ker = G →
        Function.Injective (tmap l A B q) ∧ Function.Bijective (vmap l q) ∧
        {x : Vl l A | vmap l q x ∈ LinearMap.range (tv l B)} = latSet l G ∧
        ∀ (l' : ℕ) [Fact l'.Prime], l' ≠ l → (l' : K) ≠ 0 → Function.Bijective (tmap l' A B q))

example : IsAlgClosed (AlgebraicClosure (ZMod 3)) := inferInstance

end GlobalTheory.AV.LTors
