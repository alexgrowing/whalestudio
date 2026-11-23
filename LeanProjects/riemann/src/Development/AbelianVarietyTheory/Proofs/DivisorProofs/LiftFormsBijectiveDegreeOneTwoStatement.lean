import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsBijectiveDegreeOneTwo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftForms_bijective_degree_one_two : ∀ (D : Data) (Λ : Lift D) (U : AffOp D.X), Function.Bijective (fun ω : Ω[Sec D.s U.unop.1⁄D.R] ↦ (Submodule.Quotient.mk ((Λ.semi U).m1 ω) : K1 D.R (Λ.L.obj U).δ)) ∧ Function.Bijective (fun x : Om D.R (Sec D.s U.unop.1) 2 ↦ (Submodule.Quotient.mk ((Λ.semi U).mOm 2 x) : K D.R (Λ.L.obj U).δ 2)) := by
  first | exact @GlobalTheory.PDForm.lift_forms_bij | exact GlobalTheory.PDForm.lift_forms_bij | (intros; apply GlobalTheory.PDForm.lift_forms_bij <;> assumption)
