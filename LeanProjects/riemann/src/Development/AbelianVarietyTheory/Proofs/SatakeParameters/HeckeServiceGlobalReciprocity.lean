import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReciprocityKernelServiceStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowHServOfKerServ
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory

theorem row_hServ_of_link : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Lk : LkT Bundle),
    (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → LinkR p K β c b.R) →
    R1.SerreConditionAtBundlePoints (IsGoodE p.s) Lk := by
  intro hA hL p Lk hLk
  have h1 := Row.map (Bd := Bundle) (Q := IsGoodE p.s) (Lk := Lk) (Bd' := BdRec) (Q' := IsGoodE p.s) (Lk' := LinkR p)
    (fun _ _ _ b => b.R) (fun _ _ _ _ _ h => h) (fun K β c b _ h => hLk K β c b h) (GlobalTheory.T.reciprocity_kernel_service hA p)
  exact GlobalTheory.Fc.R1.row_hServ_of_kerServ _ Lk h1
end GlobalTheory
