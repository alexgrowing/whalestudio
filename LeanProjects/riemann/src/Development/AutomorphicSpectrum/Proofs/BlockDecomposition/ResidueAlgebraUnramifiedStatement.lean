import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_algebra_unramified : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | exact GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | (intros; apply GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad <;> assumption)
