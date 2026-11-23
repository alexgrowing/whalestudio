import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoint_frames_move_integralRightTranslate : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  first | exact @GlobalTheory.FrameShift.exists_pt_mul | exact GlobalTheory.FrameShift.exists_pt_mul | (intros; apply GlobalTheory.FrameShift.exists_pt_mul <;> assumption)
