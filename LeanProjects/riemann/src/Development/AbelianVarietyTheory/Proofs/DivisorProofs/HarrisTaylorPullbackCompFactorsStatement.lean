import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorPullback_comp_factors : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₀ S₁ T : Scheme.{0}) (s₀ : S₀ ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (t : T ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o : GlobalTheory.UPel.HT.Obj b N t) (g : S₁ ⟶ S₀) (h : T ⟶ S₁), GlobalTheory.UPel.HT.ObjMap o₁ o₀ g → GlobalTheory.UPel.HT.ObjMap o o₀ (h ≫ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o o₁ h) := by
  first | exact @GlobalTheory.UPel.HT.PullFactor.objMap_factor | exact GlobalTheory.UPel.HT.PullFactor.objMap_factor | (intros; apply GlobalTheory.UPel.HT.PullFactor.objMap_factor <;> assumption)
