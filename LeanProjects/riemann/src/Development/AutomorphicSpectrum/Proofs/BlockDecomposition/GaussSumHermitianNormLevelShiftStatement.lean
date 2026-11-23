import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelShift
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_hermitian_norm_level_shift : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ (j + 2), ψ (j + 2) (Ideal.Quotient.mk (lev ϖ (j + 2)) a * (barσ σ ϖ hR.fix_ϖ (j + 2) w * w))) = (q : ℂ) ^ 2 * ∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussRec.gauss_recursion | exact GlobalTheory.CompanionTheory.GaussRec.gauss_recursion | (intros; apply GlobalTheory.CompanionTheory.GaussRec.gauss_recursion <;> assumption)
