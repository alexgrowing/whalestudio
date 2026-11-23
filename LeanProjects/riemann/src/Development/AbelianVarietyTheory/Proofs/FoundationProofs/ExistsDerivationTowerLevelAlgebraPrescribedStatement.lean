import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribed
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module (integralClosure (O0 p) Ω) M] (μ ν : M), (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0 → ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0 → ∃ D : (integralClosure (O0 p) Ω) → M, IsDerOn (levelAlg T n) D ∧ D (zS T n) = μ ∧ D (qS T n) = ν := by
  first | exact @GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | exact GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | (intros; apply GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg <;> assumption)
