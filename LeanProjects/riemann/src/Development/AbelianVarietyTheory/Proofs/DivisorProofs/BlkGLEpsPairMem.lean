import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem JR_dblSp_gram {D : D7} (S : HSp D) :
    JR (F := D.host.F) (AF D.host.F) (dblSp S).gram =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) := by
  rw [show (dblSp S).gram = dblGram finSumFinEquiv S.gram from gram_hdbl S, dblGram, JR,
    blkMat_map _ _ (map_zero _)]
  simp [JR, Matrix.map_neg]

theorem neg_one_mem_UJ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) : (-1 : GL n A) ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (-1 : GL n A).val * J * (-1 : GL n A).val = J
  rw [Units.val_neg, Units.val_one, Formalism.UG.cT, Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ),
    Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

def epsPair {D : D7} (S : HSp D) : GL (Fin S.rank) (AE D) × GL (Fin S.rank) (AE D) := (1, -1)

theorem blkGL_epsPair_mem {D : D7} (S : HSp D) :
    blkGL finSumFinEquiv (epsPair S) ∈
      Formalism.UG.UJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (F := D.host.F) (AF D.host.F) (dblSp S).gram) := by
  rw [JR_dblSp_gram, epsPair, blkGL_mem_UJ]
  exact ⟨one_mem _, neg_one_mem_UJ _ _⟩

def epsD {D : D7} (S : HSp D) : GA D (dblSp S) := ⟨blkGL finSumFinEquiv (epsPair S), blkGL_epsPair_mem S⟩

theorem mt_epsD {D : D7} (S : HSp D) :
    Formalism.L2.Theta.mt (dblSp S) (epsD S) =
      blkMat finSumFinEquiv (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (-1) := rfl

end GlobalTheory.DiagThetaRule
