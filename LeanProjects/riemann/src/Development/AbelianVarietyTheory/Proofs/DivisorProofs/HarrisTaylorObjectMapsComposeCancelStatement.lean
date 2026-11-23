import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harris_taylor_object_maps_compose_cancel : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (o₃ : GlobalTheory.UPel.HT.Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g))) ∧ (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_cancel | exact GlobalTheory.UPel.HT.objMap_comp_cancel | (intros; apply GlobalTheory.UPel.HT.objMap_comp_cancel <;> assumption)
