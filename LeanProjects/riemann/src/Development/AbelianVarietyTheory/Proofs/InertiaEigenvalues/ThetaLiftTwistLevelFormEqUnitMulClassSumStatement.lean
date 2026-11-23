import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftTwistLevelFormEqUnitMulClassSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_twistLevelForm_eq_unit_mul_classSum : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf X.R.toRealDat j B → ∀ (ψ : Twist D Circle) (t : X.T), ψ.Good → B.admitted ψ.Q → IsTupOf X.R.toRealDat B ψ t →
  ∀ ω : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), IsClassSystem (Vc D j) (B.levJ ψ) rep → ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ),
  ∃ (z : GA D (Vc D j)) (a : ℂ), IsCentAt j (X.R.Q t) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime X.R.toRealDat t) a ∧ ∀ y : (X.R.HV j t).H,
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y h)) ∈ B.formsC ψ →
    X.R.thF j t y (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) =
      a • B.classSum ω ψ rep (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * finPt (Vc D j) z))) := by
  first | exact @GlobalTheory.LiftClassSumTwist.thF_eq_classSum | exact GlobalTheory.LiftClassSumTwist.thF_eq_classSum | (intros; apply GlobalTheory.LiftClassSumTwist.thF_eq_classSum <;> assumption)
