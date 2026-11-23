import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → X.fm.seenP w = true → ∀ (V : Finset X.A.vT) (v : X.A.vT), v ∈ V → ∀ p, ∀ y ∈ Co.valB w V p, ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • y ∈ Co.valB w (V.erase v) p := by
  first | exact @GlobalTheory.LvT.pow_smul_mem_valB_erase | exact GlobalTheory.LvT.pow_smul_mem_valB_erase | (intros; apply GlobalTheory.LvT.pow_smul_mem_valB_erase <;> assumption)
