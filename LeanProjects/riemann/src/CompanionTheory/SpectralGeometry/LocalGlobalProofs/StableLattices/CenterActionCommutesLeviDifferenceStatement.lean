import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_action_commutes_levi_difference : ∀ (n M : ℕ) (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ), Monotone lev →
    (∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      (∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) (ev E (fa n Y))) ∧
      ∀ x : V, ∃ w : Pos n → V, ev E (fa n Y) x - evL lev E (fb d h Y) x =
        ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.co_hyp | exact GlobalTheory.CompanionTheory.RgCOBlock.co_hyp | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.co_hyp <;> assumption)
