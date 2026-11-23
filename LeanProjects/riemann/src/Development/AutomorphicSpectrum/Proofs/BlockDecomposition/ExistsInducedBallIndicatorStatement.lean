import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_induced_ball_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E), ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | exact GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | (intros; apply GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr <;> assumption)
