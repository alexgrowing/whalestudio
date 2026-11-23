import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreThetaSectionGermEqFourierRatioMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTermStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLiftImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_thetaSectionGerm_eq_fourierRatio_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → ∀ (k N : ℕ) (α : Fin N → D.toPre.X) (b : ∀ j, D.toPre.SecB k (α j)) (τ : Fin N → SecK D.toPre.P.L Y.q.left k) (F : Fin N → IntFam (maximalIdeal R) D.toPre k) (s : Fin N → H0 U.LG.L k), (∀ j, IsTermOf Y (b j) (τ j)) → (∀ j, (F j).Lead (α j) (b j)) → (∀ j, U.ExpandsAt 0 k (s j) (F j).f) → ∀ (z : (thickObj R (maximalIdeal R) 0 G).left) (j : Fin N) (i : Fin 1 → U.LG.L.ι), ψ.left z ∈ nonzeroLocus (τ j) → (fstG (maximalIdeal R) 0 G).left z ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s l) i = gs (Y := (thickObj R (maximalIdeal R) 0 G).left) ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i := by
  first | exact @GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul | exact GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul | (intros; apply GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul <;> assumption)
