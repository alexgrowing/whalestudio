import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianRelDimEqOfGrpPullbackField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelian_relDim_eq_of_grpPullback_field : ∀ (K : Type) [Field K] (S : Scheme.{0}) (f : Sp K ⟶ S) (P : PolAV S) (P' : PolAV (Sp K)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → P'.g = P.g := by
  first | exact @GlobalTheory.PolDim.g_eq_of_isGrpPullback | exact GlobalTheory.PolDim.g_eq_of_isGrpPullback | (intros; apply GlobalTheory.PolDim.g_eq_of_isGrpPullback <;> assumption)
