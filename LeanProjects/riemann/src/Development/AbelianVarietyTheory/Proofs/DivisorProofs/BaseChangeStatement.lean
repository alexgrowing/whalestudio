import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_ev_of_isPullback : ∀ (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S''), Rep A b P → IsPullback k b'' b h → Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  first | exact @GlobalTheory.DualCon.Rep.baseChange | exact GlobalTheory.DualCon.Rep.baseChange | (intros; apply GlobalTheory.DualCon.Rep.baseChange <;> assumption)
