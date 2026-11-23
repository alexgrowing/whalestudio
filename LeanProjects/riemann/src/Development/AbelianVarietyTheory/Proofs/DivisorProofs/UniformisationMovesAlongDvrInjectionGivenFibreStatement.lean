import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationMovesAlongDvrInjectionGivenFibre
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
theorem _root_.GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → ∀ (φ : V →+* V') (φK : FractionRing V →+* FractionRing V'), φK.comp (algebraMap V _) = (algebraMap V' _).comp φ → (maximalIdeal V).map φ ≤ maximalIdeal V' → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (A' : PolAV (Sp (FractionRing V'))) (ψ : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap φK) ψ → LBIso A'.L (A.L.pull ψ) → A'.g = A.g → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing V') F], (algebraMap (FractionRing V') F).comp φK = algebraMap (FractionRing V) F → ∃ (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg φ D.toPre D'.toPre) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal V') D' A' G'), IsSemiAbelian G' ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (q : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F k q x → ∃ (q' : QkPt D'.toPre F k) (x' : TFK (R := V') F ⟶ A'.A), hD.xe q'.y = q.y ∧ x'.left ≫ ψ = x.left ∧ QkToAkU U'.toUnifPre F k q' x' := by
  first | exact @GlobalTheory.UnifMoveGiven.move_given | exact GlobalTheory.UnifMoveGiven.move_given | (intros; apply GlobalTheory.UnifMoveGiven.move_given <;> assumption)
