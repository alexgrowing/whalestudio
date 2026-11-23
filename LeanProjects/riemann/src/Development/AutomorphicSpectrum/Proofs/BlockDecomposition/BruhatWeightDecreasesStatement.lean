import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreases
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bruhat_weight_decreases : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t w w' b r i : GU σ n) (π π' : Equiv.Perm (Fin n)), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → IsPermW w π → IsPermW w' π' → IsBorelU b → r ∈ IwU σ n → i ∈ IwU σ n → w * r * t = b * w' * i → permWt t π' < permWt t π ∨ (π' = π ∧ ∀ a : Fin n, ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))) := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.cell_triang | exact GlobalTheory.CompanionTheory.SatPow.cell_triang | (intros; apply GlobalTheory.CompanionTheory.SatPow.cell_triang <;> assumption)
