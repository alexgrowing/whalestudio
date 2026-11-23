import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerRmulBorel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_rmul_borel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  first | exact @GlobalTheory.ScalarPoin.qS_rmul | exact GlobalTheory.ScalarPoin.qS_rmul | (intros; apply GlobalTheory.ScalarPoin.qS_rmul <;> assumption)
