import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateLogNeZero
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_log_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (hπ : Irreducible π) (f : PowerSeries ↥(OL K))
    (hf : IsLubinTateSeries π f) (x : AK K) (hx : thetaK K x = 0), x ∉ RingHom.ker (thetaK K) ^ 2 → ltLog hπ hf x hx ≠ 0 := by
  first | exact @GlobalTheory.LogFirstOrder.ltLog_ne_zero | exact GlobalTheory.LogFirstOrder.ltLog_ne_zero | (intros; apply GlobalTheory.LogFirstOrder.ltLog_ne_zero <;> assumption)
