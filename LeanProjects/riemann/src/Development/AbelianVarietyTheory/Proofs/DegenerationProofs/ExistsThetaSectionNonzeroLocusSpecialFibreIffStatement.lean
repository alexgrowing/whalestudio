import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroLocusSpecialFibreIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSection_nonzeroLocus_specialFibre_iff : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), ∃ θ : LB.Sec D.toPre.P.L, ∀ y : (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, (fstG (IsLocalRing.maximalIdeal V) 0 G).left y ∈ nonzeroLocus ϑ ↔ (U.gt 0).pG.left y ∈ nonzeroLocus θ := by
  first | exact @GlobalTheory.SpecialFibreLocus.exists_sec_nonzeroLocus_iff | exact GlobalTheory.SpecialFibreLocus.exists_sec_nonzeroLocus_iff | (intros; apply GlobalTheory.SpecialFibreLocus.exists_sec_nonzeroLocus_iff <;> assumption)
