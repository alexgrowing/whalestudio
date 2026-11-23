import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal

theorem GlobalTheory.LocM.FJ.factor_affineOpen_of_closedPoint_mem : ∀ (X : Scheme.{0}) (A : Type) [CommRing A] [IsLocalRing A] (z : Sp A ⟶ X) (U : X.Opens) (hU : IsAffineOpen U), z (IsLocalRing.closedPoint A) ∈ U → ∃ φ : Γ(X, U) →+* A, spMap φ ≫ hU.fromSpec = z := by
  intro X A _ _ z U hU hz
  have hr : Set.range z.base ⊆ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    have hs : a ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint a
    exact (hs.map z.continuous).mem_open U.2 hz
  let g : Sp A ⟶ Spec Γ(X, U) := IsOpenImmersion.lift hU.fromSpec z hr
  refine ⟨(Spec.preimage g).hom, ?_⟩
  have h1 : spMap (Spec.preimage g).hom = g := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage g).hom) = g
    rw [CommRingCat.ofHom_hom]
    exact Spec.map_preimage g
  rw [h1]
  exact IsOpenImmersion.lift_fac _ _ _
