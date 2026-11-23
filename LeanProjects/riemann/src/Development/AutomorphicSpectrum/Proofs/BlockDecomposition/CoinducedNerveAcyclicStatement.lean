import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedNerveAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinduced_nerve_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | exact GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind <;> assumption)
