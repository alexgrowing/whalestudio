import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePointOfLevelLiftHarrisTaylor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_point_of_level_lift_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), 3 ≤ N → ∀ (hd : N ∣ N') (hc : N'.Coprime p) (M : Model b N) (M' : Model b N') (π : M'.X ⟶ M.X), π ≫ M.s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) M.univ π) (T : Over M.X) (lv : D.La → (T ⟶ M.univ.A)), IsLift M.univ N' T lv → ∃ g : T.left ⟶ M'.X, g ≫ π = T.hom ∧ ∀ a, (lv a).left = g ≫ (M'.univ.eta a).left ≫ om.φ := by
  first | exact @GlobalTheory.UPel.HT.OfLift.ofLift | exact GlobalTheory.UPel.HT.OfLift.ofLift | (intros; apply GlobalTheory.UPel.HT.OfLift.ofLift <;> assumption)
