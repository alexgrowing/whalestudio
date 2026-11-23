import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeAdelicVectorSizeProductMulUnitaryQuotientHeigh
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_adelicVectorSizeProduct_mul_unitaryQuotientHeight_pow : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V) (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N := by
  first | exact @GlobalTheory.SeenSize.le_vsize_mul_quotHeight | exact GlobalTheory.SeenSize.le_vsize_mul_quotHeight | (intros; apply GlobalTheory.SeenSize.le_vsize_mul_quotHeight <;> assumption)
