import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBound
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_of_norm_bound : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ ν : Fin n → ℤ, Antitone ν → DomLE (wtR ν) (m0 lam) → ∀ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) → ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (wtR ν (w a) - rhoV n (w a) + rhoV n a) ^ 2 → ν ∈ harmZ lam := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | exact GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | (intros; apply GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge <;> assumption)
