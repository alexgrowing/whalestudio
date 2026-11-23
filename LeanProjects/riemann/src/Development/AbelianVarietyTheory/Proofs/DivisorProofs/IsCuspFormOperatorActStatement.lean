import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorAct
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspForm_operator_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (o : Op E a) (φ : Sm E a), IsCuspForm φ → IsCuspForm (act o φ) := by
  first | exact @GlobalTheory.CuspStabFin.isCuspForm_act | exact GlobalTheory.CuspStabFin.isCuspForm_act | (intros; apply GlobalTheory.CuspStabFin.isCuspForm_act <;> assumption)
