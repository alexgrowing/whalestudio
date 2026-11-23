import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivity
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSum_of_compactCoefficient_positivity : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base G → (∀ y, 0 < nn y) → TBB.BlockGrowthBound p nn G Y K N := by
  first | exact @GlobalTheory.LatticeGerm.latticeSum_of_cptCoef | exact GlobalTheory.LatticeGerm.latticeSum_of_cptCoef | (intros; apply GlobalTheory.LatticeGerm.latticeSum_of_cptCoef <;> assumption)
