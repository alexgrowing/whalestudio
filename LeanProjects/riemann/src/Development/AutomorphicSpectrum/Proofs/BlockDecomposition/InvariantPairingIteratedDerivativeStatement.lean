import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingIteratedDerivative
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_iterated_derivative : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (π π' : GRep k (((m + 1) + m) + 1))
    (hs : IsSmooth π.ρ) (hs' : IsSmooth π'.ρ) (B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π.ρ g v) (π'.ρ g v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0),
    ∃ B' : (iterN ψ m (gres π)).V →ₗ[ℂ] (iterN ψ⁻¹ m (gres π')).V →ₗ[ℂ] ℂ,
      (∀ p v v', B' ((iterN ψ m (gres π)).ρ p v) ((iterN ψ⁻¹ m (gres π')).ρ p v') = B' v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B' v v' ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZShell.pair_iterN | exact GlobalTheory.CompanionTheory.BZShell.pair_iterN | (intros; apply GlobalTheory.CompanionTheory.BZShell.pair_iterN <;> assumption)
