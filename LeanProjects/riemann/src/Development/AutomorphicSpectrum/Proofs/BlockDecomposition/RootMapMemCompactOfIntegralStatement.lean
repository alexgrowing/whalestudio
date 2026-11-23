import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootMapMemCompactOfIntegral
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_map_mem_compact_of_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.uR_mem_KU | exact GlobalTheory.CompanionTheory.SwapRoot.uR_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.uR_mem_KU <;> assumption)
