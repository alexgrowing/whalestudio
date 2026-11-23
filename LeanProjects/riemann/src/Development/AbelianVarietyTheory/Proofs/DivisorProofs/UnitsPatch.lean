import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

def Cond {X X' Z : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) : Prop :=
  ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W) ∧
    ∀ x : Γ(X, W), i.app W x = 0 → ∀ r : Γ(X', p ⁻¹ᵁ W), ∃ y : Γ(X, W), i.app W y = 0 ∧ p.app W y = p.app W x * r

def UnitsPatch {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) : Prop :=
  ∀ W : X.Opens, Function.Injective (pullU p W) ∧
    ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) → ∃ u : Γ(X, W)ˣ, pullU p W u = u'

def LocGen {Y : Scheme.{0}} (L : LB Y) (V : Y.Opens) (a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ) : Prop :=
  ∀ (y : Y) (k k' : L.ι), y ∈ V → y ∈ L.U k → y ∈ L.U k' →
    gm (𝟙 Y) y (V ⊓ L.U k) (a k) = gm (𝟙 Y) y (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) y (V ⊓ L.U k') (a k')

def Matches {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) {L' : LB X'} {N : LB Z}
    (w : LB.Iso (L'.pull i') (N.pull p')) {V' : X'.Opens} {V : Z.Opens} (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ)
    (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ) : Prop :=
  ∀ (z : Z') (k : L'.ι) (l : N.ι), i' z ∈ V' → p' z ∈ V → i' z ∈ L'.U k → p' z ∈ N.U l →
    gm p' z (V ⊓ N.U l) (b l) =
      gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) *
        gm i' z (V' ⊓ L'.U k) (a k)

def Pinched (g : ℕ) {S S' Z B' C Y : Scheme.{0}} (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z)
    (i : Y ⟶ B') (q : Y ⟶ C) (x : B') : Prop :=
  ∃ (U U' V : Scheme.{0}) (u : U ⟶ S) (p : U' ⟶ U) (j : U' ⟶ B') (n : V ⟶ U) (k : V ⟶ C),
    SmoothOfRelativeDimension g u ∧ IsPullback p (j ≫ b') u s' ∧ IsOpenImmersion j ∧ x ∈ Set.range j ∧
    IsPullback n (k ≫ e) u z ∧
    ∀ (T : Scheme.{0}) (a : T ⟶ U') (a' : T ⟶ V), a ≫ p = a' ≫ n → ∃ y : T ⟶ Y, y ≫ i = a ≫ j ∧ y ≫ q = a' ≫ k

end GlobalTheory.Pinch
