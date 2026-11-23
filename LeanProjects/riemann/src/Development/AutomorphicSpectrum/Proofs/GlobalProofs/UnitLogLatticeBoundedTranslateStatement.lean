import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitLogLatticeBoundedTranslate
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_log_lattice_bounded_translate : ∀ (F : Type) [Field F] [NumberField F] (e : ℕ), 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : logSpace F, ∃ u : (𝓞 F)ˣ,
    ∀ w, |y w + (e : ℝ) * logEmbedding F (Additive.ofMul u) w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense <;> assumption)
