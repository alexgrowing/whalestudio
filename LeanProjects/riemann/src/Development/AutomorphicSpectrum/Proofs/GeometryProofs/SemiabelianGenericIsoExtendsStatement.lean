import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianGenericIsoExtends
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_generic_iso_extends : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) (x : Sp V ⟶ X) (x' : Sp V ⟶ X') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (φ' : GK.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap V K) ≫ x) φ → IsGrpPullback GK G' (spMap (algebraMap V K) ≫ x') φ' → ∃ (G₀ : Over (Sp V)) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left) (ψ' : G₀.left ⟶ G'.left) (κ : GK.left ⟶ G₀.left), IsGrpPullback G₀ G x ψ ∧ IsGrpPullback G₀ G' x' ψ' ∧ IsGrpPullback GK G₀ (spMap (algebraMap V K)) κ ∧ κ ≫ ψ = φ ∧ κ ≫ ψ' = φ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel | exact GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel | (intros; apply GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel <;> assumption)
