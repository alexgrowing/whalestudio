import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviSubspaceInvariantUnderBlocks
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_subspace_invariant_under_blocks : ∀ {n : ℕ} (P : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (χ : Fin n → ℂ) (L : Fin n → Fin 3) (a b : Fin n), blk (stdBlocks d h) a = blk (stdBlocks d h) b → ∀ x ∈ leviSub P d h χ L, P.E a b x ∈ leviSub P d h χ L := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | exact GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | (intros; apply GlobalTheory.CompanionTheory.RgTransport.leviSub_stable <;> assumption)
