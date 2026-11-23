import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReciprocityKernelService
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocity_kernel_service : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL), Row (Bd := BdRec) (IsGoodE p.s) (LinkR p) (ServH (Bd := BdRec) fun _ _ _ R => R.T.ker) := by
  first | exact @GlobalTheory.Svd.servH_row_linkR | exact GlobalTheory.Svd.servH_row_linkR | (intros; apply GlobalTheory.Svd.servH_row_linkR <;> assumption)
