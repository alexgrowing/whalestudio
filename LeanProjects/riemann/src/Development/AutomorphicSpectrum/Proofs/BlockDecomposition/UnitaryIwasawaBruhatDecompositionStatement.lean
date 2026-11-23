import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwasawaBruhatDecomposition
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_bruhat_decomposition : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ g : GU σ n, ∃ (b w i : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU b ∧ IsPermW w π ∧ i ∈ IwU σ n ∧ g = b * w * i := by
  first | exact @GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa | exact GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa | (intros; apply GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa <;> assumption)
