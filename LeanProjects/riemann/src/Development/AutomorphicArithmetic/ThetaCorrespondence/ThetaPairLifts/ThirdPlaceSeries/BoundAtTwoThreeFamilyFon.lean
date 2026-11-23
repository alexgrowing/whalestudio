import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.NLink
variable {D : D7}
structure SetupAlt (L : SizeData₂ D) (nch : NChoice D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (C₂ : ℝ) : Prop where
  facts : _root_.GlobalTheory.NFacts.NormChoiceFacts D nch
  canon : GlobalTheory.HubX.Canon L HW (rowC C₂) X
  par : AdmissibleParameterJ.AdmPar L
  par67 : EmbeddingTypeJumps.ParametersPolynomiallyBounded L
  big : 8 ≤ L.sc.L
  split : 60 ≤ D.host.splitBound
  kill : KillingConditions.KillAt X.ρ
  sha : TwistedPlaces.ShaFinOdd D
def ExtraAlt (D : D7) (C : ℝ) (CT : ℕ) : Prop := KillingConditions.CommutingEndomorphismCondition D ∧ _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT
def FactsFAlt {eps : ℝ} (Fm : FamP eps) (C : ℝ) (CT : ℕ) : Prop :=
  ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch ∧ _root_.GlobalTheory.NLink.ExtraAlt (Fm.D x i) C CT
def BoundAtTwoThreeFamilyFonAlt {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ → BoundAtTwoThree (Fm.L x i) X.ρ C
theorem BoundAtTwoThreeFamilyFonAlt.of_all {eps : ℝ} {Fm : FamP eps} (h : BoundAtTwoThreeFamily Fm) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm := by
  obtain ⟨C, x0, h⟩ := h
  exact ⟨C, x0, fun x hx0 _ i _ _ _ X _ S => h x hx0 i S.sha X.r X.ρ S.canon.fam S.kill⟩
end GlobalTheory.NLink
end
end
