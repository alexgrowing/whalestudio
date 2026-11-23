import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absoluteThetaIntegral_le_continuousSeminorm : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧ ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  first | exact @GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | exact GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | (intros; apply GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm <;> assumption)
