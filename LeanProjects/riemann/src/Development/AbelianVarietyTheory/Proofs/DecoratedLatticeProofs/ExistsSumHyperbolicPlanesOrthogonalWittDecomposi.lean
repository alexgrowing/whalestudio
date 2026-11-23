import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.HypSumWitt

open scoped ComplexOrder

theorem gramAt_hypSp (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ =
      (Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  unfold gramAt
  rw [GlobalTheory.Doubling.gram_hdbl]
  ext i j
  simp [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, GlobalTheory.OrthSumSp.posSp_gram]
  generalize finSumFinEquiv.symm i = a
  generalize finSumFinEquiv.symm j = b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, apply_ite]

theorem gsq (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ * gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ = 1 := by
  rw [gramAt_hypSp, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem gct (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    (gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ)ᴴ = gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ := by
  rw [gramAt_hypSp, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  simp

theorem exists_hypSum_orthDec_hypDec : ∀ (D : D7) (W : HSp D) (t : ℕ), HSpace.SigOK W → ∃ (H B : HSp D) (_ : OrthDec B W H) (_ : HypDec B W t), HSpace.SigOK H ∧ HSpace.SigOK B ∧ H.rank = 2 * t ∧ (∀ τ, H.sig τ = (t, t)) ∧ ∃ sH : RealMat H, ∀ τ, IsCartanInv (gramAt D H τ) (sH τ) := by
  intro D W t hW
  refine ⟨GlobalTheory.OrthSumSp.hypSp D t, _, GlobalTheory.OrthSumSp.orthSumDec D W _, GlobalTheory.OrthSumSp.hypSumDec D W t,
    GlobalTheory.OrthSumSp.hypSp_sigOK D t, GlobalTheory.Doubling.sigOK_hsum hW (GlobalTheory.OrthSumSp.hypSp_sigOK D t), ?_,
    GlobalTheory.OrthSumSp.hypSp_sig D t, fun τ => gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ, fun τ => ⟨gsq D t τ, ?_, ?_⟩⟩
  · show t + t = 2 * t; omega
  · rw [gct, Matrix.mul_assoc, gsq, Matrix.mul_one]
  · rw [gsq]; exact Matrix.PosDef.one
end GlobalTheory.HypSumWitt
