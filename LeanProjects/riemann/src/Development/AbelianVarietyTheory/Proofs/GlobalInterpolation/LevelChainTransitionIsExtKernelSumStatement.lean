import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSum
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChainTransition_isExt_kernel_sum : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (M' : PtModel X (i + 1)) (K : KerPt M M') (φ : Fn X i) (Φ : M.Pt → M.Val), K.TgtEq → M.IsExt φ Φ → M'.IsExt (KT X i φ) (fun p' => ∑ c, X.C.wt i c • K.k (M.rep c) p' (Φ (M.rep c))) := by
  first | exact @GlobalTheory.LvT.isExt_KT | exact GlobalTheory.LvT.isExt_KT | (intros; apply GlobalTheory.LvT.isExt_KT <;> assumption)
