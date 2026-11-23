import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionRootDiagonalConj
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reflection_root_diagonal_conj : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ t : GU σ n, PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) →
    ∃ c : L, c ≠ 0 ∧ ∃ t' : GU σ n, IsBorelU t' ∧
      (∀ x : L, sR σ hU.1 a h * uR σ hU.1 a h x * t = t' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x))) ∧
      chiDeltaU q (fun k => (χ k : ℂ)) t' * (q : ℂ) ^ (2 * ordL c) =
        chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.Torus.torus_step | exact GlobalTheory.CompanionTheory.SwapRoot.Torus.torus_step | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.Torus.torus_step <;> assumption)
