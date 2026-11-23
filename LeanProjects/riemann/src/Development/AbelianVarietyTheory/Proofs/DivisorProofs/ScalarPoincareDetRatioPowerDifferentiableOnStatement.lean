import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerDifferentiableOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom := by
  first | exact @GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | exact GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | (intros; apply GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn <;> assumption)
