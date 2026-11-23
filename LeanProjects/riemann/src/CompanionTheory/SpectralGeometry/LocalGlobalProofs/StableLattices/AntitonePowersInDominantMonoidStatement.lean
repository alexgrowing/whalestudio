import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antitone_powers_in_dominant_monoid : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (a : Fin n → ℤ), Antitone a → GlobalTheory.CompanionTheory.CartGL.dPow p a ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure | exact GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure | (intros; apply GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure <;> assumption)
