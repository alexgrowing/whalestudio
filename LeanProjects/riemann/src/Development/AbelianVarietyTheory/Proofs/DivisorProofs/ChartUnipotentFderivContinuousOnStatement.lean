import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_unipotent_fderiv_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) := by
  first | exact @GlobalTheory.CuspRep.JointCont.chart_jointCont | exact GlobalTheory.CuspRep.JointCont.chart_jointCont | (intros; apply GlobalTheory.CuspRep.JointCont.chart_jointCont <;> assumption)
