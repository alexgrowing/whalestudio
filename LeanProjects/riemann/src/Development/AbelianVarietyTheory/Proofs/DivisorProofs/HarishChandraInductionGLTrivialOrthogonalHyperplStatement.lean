import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperpl
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b → ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  first | (exact @GlobalTheory.Shin.hc_one_orth_hfree) | (exact GlobalTheory.Shin.hc_one_orth_hfree) | (intros; apply GlobalTheory.Shin.hc_one_orth_hfree  <;> assumption)
