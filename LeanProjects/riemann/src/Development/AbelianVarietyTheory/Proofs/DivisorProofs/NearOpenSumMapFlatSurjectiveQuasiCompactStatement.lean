import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumMapFlatSurjectiveQuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nearOpen_sumMap_flat_surjective_quasiCompact : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), Flat (Desc.sum N p hp).left ∧ Surjective (Desc.sum N p hp).left ∧ QuasiCompact (Desc.sum N p hp).left := by
  first | exact @GlobalTheory.Mum.Desc.sum_flat_surjective_quasiCompact | exact GlobalTheory.Mum.Desc.sum_flat_surjective_quasiCompact | (intros; apply GlobalTheory.Mum.Desc.sum_flat_surjective_quasiCompact <;> assumption)
