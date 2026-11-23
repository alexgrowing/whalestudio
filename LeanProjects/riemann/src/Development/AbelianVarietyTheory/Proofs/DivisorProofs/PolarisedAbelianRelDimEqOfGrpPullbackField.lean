import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.NotRelAmpleOfNotIsProper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDim

theorem g_eq_of_isGrpPullback : ∀ (K : Type) [Field K] (S : Scheme.{0}) (f : Sp K ⟶ S) (P : PolAV S)
    (P' : PolAV (Sp K)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → P'.g = P.g := by
  intro K _ S f P P' φ h
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)
  have hd : SmoothOfRelativeDimension P.g P'.A.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P.g) h.1 P.smoothDim
  obtain ⟨s⟩ : Nonempty (Sp K) := inferInstance
  exact GlobalTheory.PolTest.dim_eq_of_nonempty s P' hd

end GlobalTheory.PolDim
