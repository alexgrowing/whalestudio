import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonCompleteDvrPadicAlgClosureUnitBalls
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
theorem _root_.GlobalTheory.T.exists_common_complete_dvr_padicAlgClosure_unitBalls : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ x : FractionRing V', ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V' (FractionRing V'))) → ∀ s : Finset (PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra (FractionRing W) (PadicAlgCl p)), IsAdicComplete (maximalIdeal W) W ∧ (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ (↑s ⊆ Set.range (algebraMap (FractionRing W) (PadicAlgCl p))) ∧ (∀ z : PadicAlgCl p, ∃ f : Polynomial (FractionRing W), f ≠ 0 ∧ Polynomial.eval₂ (algebraMap (FractionRing W) (PadicAlgCl p)) z f = 0) ∧ (∃ (φ : V →+* W) (φK : FractionRing V →+* FractionRing W), φK.comp (algebraMap V _) = (algebraMap W _).comp φ ∧ (maximalIdeal V).map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V) (PadicAlgCl p)) ∧ (∃ (φ : V' →+* W) (φK : FractionRing V' →+* FractionRing W), φK.comp (algebraMap V' _) = (algebraMap W _).comp φ ∧ (maximalIdeal V').map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V') (PadicAlgCl p)) := by
  first | exact @GlobalTheory.UnifField.exists_common_ring | exact GlobalTheory.UnifField.exists_common_ring | (intros; apply GlobalTheory.UnifField.exists_common_ring <;> assumption)
