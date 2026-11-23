import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (F : Finset (integralClosure (O0 p) Ω)), ∃ (C : Subalgebra (O0 p) (integralClosure (O0 p) Ω)) (tr : (integralClosure (O0 p) Ω) → (integralClosure (O0 p) Ω)) (n : ℕ) (a b : Fin n → (integralClosure (O0 p) Ω)), (↑F : Set (integralClosure (O0 p) Ω)) ⊆ C ∧ IsTrData (towerAlg T) C tr a b (p : (integralClosure (O0 p) Ω)) := by
  first | exact @GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg | exact GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg | (intros; apply GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg <;> assumption)
