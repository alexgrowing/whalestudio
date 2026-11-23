import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_character_times_inverse_unitary : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m), p.Rows → GlobalTheory.CovTop.RecTied D L → ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈ Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  first | exact @GlobalTheory.CovTop.chi_mul_psi_inv_mem_core | exact GlobalTheory.CovTop.chi_mul_psi_inv_mem_core | (intros; apply GlobalTheory.CovTop.chi_mul_psi_inv_mem_core <;> assumption)
