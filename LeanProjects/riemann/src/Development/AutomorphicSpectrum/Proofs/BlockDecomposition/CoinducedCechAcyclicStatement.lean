import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedCechAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinduced_cech_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Surjective e → ∀ (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology <;> assumption)
