import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryProdCreationLeviChains
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_prod_creation_levi_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (l : List (Pos n)) (x : Cq n V), (∀ e ∈ l, lev e.1.1 = lev e.1.2) →
    (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
      CompanionTheory.RgExh.U.adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
    SuppL (inUU lev) x → (∀ e ∈ l, Lv lev E1 E2 e.1.1 e.1.2 x = 0) →
    bdL (inRR lev) E1 E2 (((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) x) =
      (-1 : ℂ) ^ l.length • ((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V))
        (bdL (inRR lev) E1 E2 x) := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.BdProdL.bd_prodL | exact GlobalTheory.CompanionTheory.LvChain.BdProdL.bd_prodL | (intros; apply GlobalTheory.CompanionTheory.LvChain.BdProdL.bd_prodL <;> assumption)
