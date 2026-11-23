import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_moduliMap_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
  (S S₁ Y : Scheme.{0}) (t : S ⟶ Sp R) (sY : Y ⟶ Sp R) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga]
  (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (o : Obj b N t) (o' : Obj b N (π₁ ≫ t)) (u : Obj b N sY),
  3 ≤ N → N.Coprime p → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → ObjMap o' o π₁ → ObjMap o' u (π₁ ≫ f) →
  Nonempty (ObjMap o u f) := by
  first | (exact @GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover) | (exact GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover) | (intros; apply GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover  <;> assumption)
