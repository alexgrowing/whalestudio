import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftOfObstructionEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  first | exact @GlobalTheory.LBLift.lift_of_isObU_zero | exact GlobalTheory.LBLift.lift_of_isObU_zero | (intros; apply GlobalTheory.LBLift.lift_of_isObU_zero <;> assumption)
