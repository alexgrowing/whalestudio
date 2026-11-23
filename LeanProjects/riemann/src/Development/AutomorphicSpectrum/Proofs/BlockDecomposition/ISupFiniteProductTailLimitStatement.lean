import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSup_finite_product_tail_limit : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι), Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) → (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) → ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) * ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) = ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  first | exact @GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | exact GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | (intros; apply GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails <;> assumption)
