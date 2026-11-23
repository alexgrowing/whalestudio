import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlat
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_of_associated_germs_flat : ∀ (X Y : Scheme.{0}) [IsIntegral X] (f : Y ⟶ X) [Flat f] [Surjective f] (L L' : LB X) (s : L.Sec) (s' : L'.Sec), L.IsLB → L'.IsLB → (∃ i, s.f i ≠ 0) → (∀ y : Y, ∃ i i', f y ∈ L.U i ∧ f y ∈ L'.U i' ∧ Associated (gs f y (L.U i) (s.f i)) (gs f y (L'.U i') (s'.f i'))) → LBIso L L' := by
  first | exact @GlobalTheory.AssocDescent.lbIso_of_associated | exact GlobalTheory.AssocDescent.lbIso_of_associated | (intros; apply GlobalTheory.AssocDescent.lbIso_of_associated <;> assumption)
