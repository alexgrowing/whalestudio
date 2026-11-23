import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_of_basicOpen_cover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
  (∀ r ∈ t, LieAt b act ((algebraMap R' (Localization.Away r)).comp β) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) →
  LieAt b act β x := by
  first | exact @GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover | exact GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover | (intros; apply GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover; all_goals assumption)
