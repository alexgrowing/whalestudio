import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_iso_of_group_pullback_generic : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (algebraMap R K)) F → ∀ (N : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B], ∃ τ : Tors G₀ N B ≃* Tors G N B, ∀ z', (τ z').1.left = z'.1.left ≫ F := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_tors_mulEquiv_of_isGrpPullback | exact GlobalTheory.GroupBplus.Aff.exists_tors_mulEquiv_of_isGrpPullback | (intros; apply GlobalTheory.GroupBplus.Aff.exists_tors_mulEquiv_of_isGrpPullback <;> assumption)
