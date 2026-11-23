import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  first | exact @GlobalTheory.PullAutConst.exists_unit | exact GlobalTheory.PullAutConst.exists_unit | (intros; apply GlobalTheory.PullAutConst.exists_unit <;> assumption)
