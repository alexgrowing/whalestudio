import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parthasarathy_rao_varadarajan : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
      (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V), Formalism.REAL.GlRel Kf →
      (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) →
      v ∈ S → v ≠ 0 → Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v →
      ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  first | exact @GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | exact GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | (intros; apply GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan <;> assumption)
