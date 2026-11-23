import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mon_hom_over_algebraic_closure : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A', IsMonHom f → ∃ g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A', IsMonHom g ∧ GlobalTheory.Spread.bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.ChowRigid.chow_rigidity | exact GlobalTheory.ChowRigid.chow_rigidity | (intros; apply GlobalTheory.ChowRigid.chow_rigidity <;> assumption)
