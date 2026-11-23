import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantOperatorBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
open scoped SchwartzMap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_invariant_operator_bound : ∀ {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V₁ ℂ) {ι : Type} [Fintype ι] (U : ι → V × V),
    (∀ (j : ι) (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.ArchUniq.schrF P (s • U j) ⇑f → T g = T f) →
    ∀ (a n : ℕ), ∃ M : ℕ, ∀ N : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ (w : V × V) (h g : SchwartzMap V ℂ),
      ⇑g = GlobalTheory.ArchUniq.schrF P w ⇑h →
      (1 + ∑ j, |GlobalTheory.ArchUniq.omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) ≤
        C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  first | exact @GlobalTheory.ArchUniq.rapidDecay_omega_of_invariant | exact GlobalTheory.ArchUniq.rapidDecay_omega_of_invariant | (intros; apply GlobalTheory.ArchUniq.rapidDecay_omega_of_invariant <;> assumption)
