import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem lbIso_pull_of_genOn (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens)
    (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ)
    (hs : ∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x))
    (hg : ∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k →
      gm f t (W x ⊓ W y) (g x y) =
        gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) :
    LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  have le : ∀ p : (PUnit → J) × L.ι, ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 ≤
      L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit) := fun p y h =>
    ⟨h.2, (mem_pull (L := (⟨J, W, g⟩ : LB X)) (F := f)).1 h.1⟩
  refine ⟨⟨fun p => res (le p) (s (p.1 PUnit.unit) p.2)⁻¹⟩, (isGen_iff_germ _).2 fun y p q hp hq => ?_⟩
  have v : ∀ p : (PUnit → J) × L.ι, y ∈ ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 →
      gm (𝟙 Y) y _ (res (le p) (s (p.1 PUnit.unit) p.2)⁻¹) =
        (gm (𝟙 Y) y (L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit)) (s (p.1 PUnit.unit) p.2))⁻¹ := fun p hp =>
    (gm_res _ y _ hp _).trans (map_inv _ _)
  have hp' := le p hp
  have hq' := le q hq
  have e1 := gm_pull_g (⟨J, W, g⟩ : LB X) f (𝟙 Y) y p.1 q.1 hp.1 hq.1
  have e2 : gm (𝟙 Y ≫ f) y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) =
      gm f y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) := by
    rw [Category.id_comp]
  have e3 := hg (p.1 PUnit.unit) (q.1 PUnit.unit) y p.2 hp'.2 hq'.2 hp'.1
  have e4 := hs (q.1 PUnit.unit) p.2 q.2 y hp'.1 hq'.1 hq'.2
  have e5 := (e1.trans e2).trans (e3.trans (congrArg (· * _) e4))
  refine (v p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·)
    ((gm_div' ((⟨J, W, g⟩ : LB X).pull f) L (𝟙 Y) y p q hp hq).trans (congrArg (· * _) e5)) (v q hq)).symm)
  have key : ∀ {G : Type} [CommGroup G] (a b c : G), c⁻¹ = a * b * c⁻¹ * a⁻¹ * b⁻¹ := by
    intro G _ a b c
    rw [mul_assoc (a * b * c⁻¹), ← mul_inv, mul_right_comm, mul_inv_cancel, _root_.one_mul]
  exact key _ _ _

end GlobalTheory.PinchLift
