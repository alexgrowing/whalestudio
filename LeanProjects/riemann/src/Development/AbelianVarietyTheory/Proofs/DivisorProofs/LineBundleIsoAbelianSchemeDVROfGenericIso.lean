import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoAb

theorem lbIso_of_generic_pullback : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Scheme.{0}) (a : A ⟶ Sp L) (φ : A ⟶ G.left), IsAbelianScheme G → IsPullback φ a G.hom (spMap (algebraMap W L)) → ∀ M M' : LB G.left, M.IsLB → M'.IsLB → LBIso (M.pull φ) (M'.pull φ) → LBIso M M' := by
  intro W L _ _ _ _ _ _ G _ A a φ hG hφ M M' hM hM' h
  have hi : pullback.fst G.hom (spMap (algebraMap W L)) = hφ.isoPullback.inv ≫ φ := hφ.isoPullback_inv_fst.symm
  have h' : LBIso (M.pull (pullback.fst G.hom (spMap (algebraMap W L))))
      (M'.pull (pullback.fst G.hom (spMap (algebraMap W L)))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp hφ.isoPullback.inv hi h
  exact GlobalTheory.GenericIsoConst.lbIso_of_generic W L G hG M M' hM hM' h'

end GlobalTheory.GenericIsoAb
