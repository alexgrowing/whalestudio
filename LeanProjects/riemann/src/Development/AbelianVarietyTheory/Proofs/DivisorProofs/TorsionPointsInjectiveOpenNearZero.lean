import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

namespace GlobalTheory.OpenOmega

theorem range_subset_range_unit {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {M : Type} [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (z : SpAlg R (TrivSqZeroExt R M) ⟶ G)
    (hz : zeroSec R M ≫ z = η[G]) : Set.range z.left ⊆ Set.range η[G].left := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨s, rfl⟩ := GlobalTheory.SqZeroPt.surjective_sec_zeroSec R M t
  refine ⟨s, ?_⟩
  rw [← hz]
  exact Scheme.Hom.comp_apply (zeroSec R M).left z.left s

theorem ptInj_of_isOpenNearZero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G]
    (GG : PDivGroup p R) (θ : TorsionMap G GG) (h : θ.IsOpenNearZero) (n : ℕ) : PtInj θ n := by
  intro M _ _ _ _ z z' hz hz' e
  obtain ⟨U, V, hU, hB⟩ := h n
  exact (hB (TrivSqZeroExt R M)).injOn ((range_subset_range_unit z.1 hz).trans hU)
    ((range_subset_range_unit z'.1 hz').trans hU) e

end GlobalTheory.OpenOmega
