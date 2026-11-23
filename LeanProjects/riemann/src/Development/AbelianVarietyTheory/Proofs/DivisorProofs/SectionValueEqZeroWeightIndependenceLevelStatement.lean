import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  first | exact @GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | exact GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | (intros; apply GlobalTheory.sval_eq_zero_of_sum_mul_coord_part <;> assumption)
