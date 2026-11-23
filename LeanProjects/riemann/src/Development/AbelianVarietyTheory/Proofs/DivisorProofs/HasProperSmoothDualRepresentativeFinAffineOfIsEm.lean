import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lbIso_of_isEmpty {X : Scheme.{0}} [IsEmpty X] (L M : LB X) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have hU : (LB.div M L).U i ⊓ (LB.div M L).U j = ⊥ := by ext x; exact (IsEmpty.false x).elim
  have : Subsingleton Γ(X, (LB.div M L).U i ⊓ (LB.div M L).U j) := by rw [hU]; infer_instance
  exact Subsingleton.elim _ _

theorem hasRepAF_of_isEmpty : ∀ (S : Scheme.{0}) (A S' : Over S) [GrpObj A] (g : ℕ), IsEmpty S'.left →
    HasRepAF A g S' := by
  intro S A S' _ g hS
  have emp : ∀ {Y : Over S} (_ : Y ⟶ S'), IsEmpty Y.left := fun y => ⟨fun p => hS.false (y.left p)⟩
  refine ⟨S', 𝟙 S', LB.triv _, ⟨⟨LB.isLB_triv _, fun Y a a' t => ?_⟩, fun T t N _ => ?_⟩, ?_, ?_⟩
  · have := emp t; exact lbIso_of_isEmpty _ _
  · have := emp (snd A T ≫ t)
    exact ⟨t, ⟨Category.comp_id _, lbIso_of_isEmpty _ _⟩, fun x hx => (Category.comp_id x).symm.trans hx.1⟩
  · rw [Over.id_left]
    refine ⟨inferInstance, ⟨fun x => isEmptyElim x⟩, ⟨?_⟩⟩
    intro K _ y Z fst snd h
    exact isEmptyElim (y (IsLocalRing.closedPoint K))
  · intro F; exact ⟨⊥, isAffineOpen_bot _, fun x _ => isEmptyElim x⟩

end GlobalTheory.DualCon
