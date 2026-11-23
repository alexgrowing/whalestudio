import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantFiniteBallSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_finite_ball_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : (Fin n → k) → E) (s S : kˣ), (∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v) → (∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) → ∃ R : Finset (Fin n → k), ∀ v : Fin n → k, φ v = ∑ x ∈ R, @ite _ (Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s) (Classical.propDecidable _) (φ x) 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates | exact GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates <;> assumption)
