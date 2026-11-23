import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerCompactReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_compact_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (C : Set (GA E n)), IsCompact C → ∃ C' : Set (GA E n), IsCompact C' ∧ ∀ t ∈ adCent d, t ∈ ((ratGL E n).range : Set (GA E n)) * C → t ∈ (ratCent d : Set (GA E n)) * C' := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul | exact GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul <;> assumption)
