import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (exact GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (intros; apply GlobalTheory.ZarhinFam.zarhin_kernel_trivial  <;> assumption)
