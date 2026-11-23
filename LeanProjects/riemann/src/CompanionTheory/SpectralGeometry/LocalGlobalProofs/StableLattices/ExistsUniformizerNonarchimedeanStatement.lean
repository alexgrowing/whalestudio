import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_nonarchimedean : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L], ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_isUnif | exact GlobalTheory.CompanionTheory.CartGL.exists_isUnif | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_isUnif <;> assumption)
