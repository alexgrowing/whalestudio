import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChains
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_adjoint_on_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    (∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) → ∀ p q : Fin n, lev p = lev q → ∀ x z : Cq n V,
      ∑ A, ⟪Lv lev E1 E2 p q x A, z A⟫_ℂ = ∑ A, ⟪x A, Lv lev E1 E2 q p z A⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint | exact GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint | (intros; apply GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint <;> assumption)
