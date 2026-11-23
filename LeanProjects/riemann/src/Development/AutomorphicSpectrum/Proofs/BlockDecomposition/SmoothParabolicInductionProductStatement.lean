import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_parabolic_induction_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), IsSmooth π₁ → IsSmooth π₂ → IsSmooth (sQ h π₁ π₂) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | exact GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | (intros; apply GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ <;> assumption)
