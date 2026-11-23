import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_service_global_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Lk : LkT Bundle), (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → LinkR p K β c b.R) → R1.SerreConditionAtBundlePoints (IsGoodE p.s) Lk := by
  first | exact @GlobalTheory.row_hServ_of_link | exact GlobalTheory.row_hServ_of_link | (intros; apply GlobalTheory.row_hServ_of_link <;> assumption)
