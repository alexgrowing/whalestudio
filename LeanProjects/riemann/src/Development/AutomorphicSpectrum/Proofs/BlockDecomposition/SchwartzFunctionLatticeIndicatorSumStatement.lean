import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionLatticeIndicatorSum
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_function_lattice_indicator_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V), ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind (latZ z (r : ℤ)) p.1 p.2 := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.schF_eq_sum_ind | exact GlobalTheory.CompanionTheory.BZCore.schF_eq_sum_ind | (intros; apply GlobalTheory.CompanionTheory.BZCore.schF_eq_sum_ind <;> assumption)
