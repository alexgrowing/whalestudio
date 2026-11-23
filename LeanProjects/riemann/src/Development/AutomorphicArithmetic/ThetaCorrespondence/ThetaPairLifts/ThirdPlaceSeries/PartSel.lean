import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3Iff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRecPins

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB
namespace GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {O : Obj D} {c : ℝ}
def BundleCondition.TiePins (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q) : Prop :=
  PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG ∧ _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q ∧ ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q, _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
abbrev BundleCondition.Comparison₂ (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Type 1 := {Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q // b.TiePins Rr}
theorem BundleCondition.Comparison₂.psi {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG := t.2.1
theorem BundleCondition.Comparison₂.pins3 {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q := t.2.2.1
theorem BundleCondition.Comparison₂.pins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := let ⟨h, _⟩ := t.2.2.2; h
theorem BundleCondition.Comparison₂.recPins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationCompatible t.pins t.1 := let ⟨_, h⟩ := t.2.2.2; h
@[reducible] def BundleCondition.part (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) : _root_.GlobalTheory.Fc.Ind.PointSummands D O c where
  R := b.R
  S := b.S
  P := b.P
  pin := b.pin
  DH := b.DH
  Dcf := b.C.c.face
  Spf := b.C.Sp
  ok1 := b.C.ok1
  B := b.B
  Rr := t.1
  psi := t.psi
  pins := t.pins
  muDef := t.pins3.muDef
  recPins := t.recPins
end Point
def HasCompatibility : BdP _root_.GlobalTheory.Fc.BundleCondition := fun _ _ _ b => Nonempty b.Comparison₂
section Sel
variable {𝒜 : FamClass}
abbrev CompatibleSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), (σ Fm hc x hx i).Comparison₂
def summandSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) (τ : _root_.GlobalTheory.Fc.CompatibleSelection σ) : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜 :=
  fun Fm hc x hx i => (σ Fm hc x hx i).part (τ Fm hc x hx i)
end Sel
section Construction₂
end Construction₂
end GlobalTheory.Fc
end
end
