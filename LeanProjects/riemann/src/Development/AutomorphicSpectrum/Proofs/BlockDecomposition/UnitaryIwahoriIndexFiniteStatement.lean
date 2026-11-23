import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFinite
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_index_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧ ∀ t : GU σ n, Finite (IwU σ n ⧸ (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.finite_index_iwU | exact GlobalTheory.CompanionTheory.SatPow.finite_index_iwU | (intros; apply GlobalTheory.CompanionTheory.SatPow.finite_index_iwU <;> assumption)
