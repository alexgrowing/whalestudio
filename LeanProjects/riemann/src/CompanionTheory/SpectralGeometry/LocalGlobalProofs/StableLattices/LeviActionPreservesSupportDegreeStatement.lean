import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegree
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_preserves_support_degree : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q, lev p = lev q → SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | exact GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg <;> assumption)
