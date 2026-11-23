import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_blocks_level_sum : ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    (∀ (i : Fin M) (p : Fin (sz lev M i)), lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ)) ∧
    ∀ (f : Fin n → ℂ) (i : Fin M), ∑ p : Fin (sz lev M i), f (stdBlocks (sz lev M) h ⟨i, p⟩) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), f a := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters | exact GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters <;> assumption)
