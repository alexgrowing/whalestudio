import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddEquivOfCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.FixedConjMat

theorem fmat_iota (D : D7) (x : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D x).2) =
      (Formalism.IndefR.Lev.finE (D.sp.Y 0) x).1 := by
  have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D x)).2
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D x) = x :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply x
  rw [hb]
  erw [e]
  ext i j
  exact GlobalTheory.RedFrame.tauF_gen (Formalism.IndefR.RationalEmbedding.inst D) _

theorem finE_val_eq (D : D7) (V : HSp D) (g : Formalism.L2.Theta.GA D V) :
    (Formalism.IndefR.Lev.finE V g).1 = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).map (Formalism.IndefR.Lev.swapAE D) := rfl

theorem map_cast_swap (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) {m n : Type}
    (M : Matrix m n (ReciprocityTheory.Aut.AL D.host.E)) :
    (M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm).map (Formalism.IndefR.Lev.swapAE D) =
      M.map (GlobalTheory.FixedConj.adeleEquiv D hF) := by
  ext i j
  rfl

theorem map_mul_eq_one {k l R S : Type} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [CommRing R]
    [CommRing S] (f : R →+* S) {A : Matrix k l R} {B : Matrix l k R} (h : A * B = 1) :
    A.map f * B.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem conj_map {k l R S : Type} [Fintype k] [Fintype l] [CommRing R] [CommRing S] (f : R →+* S)
    (T : Matrix k k S) (Ti : Matrix k k S) (B : Matrix k l R) (Y : Matrix l l R) (B' : Matrix l k R)
    (g : Matrix l l S) (hg : Y.map f = g) :
    T * (B * Y * B').map f * Ti = T * B.map f * g * (B'.map f * Ti) := by
  rw [Matrix.map_mul, Matrix.map_mul, hg]
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in

theorem finE_conj_stdPsi (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r)
    (t : Formalism.L2.Theta.GA D (Yc D 0)) (hP : StdPsi hF PY) :
    ∃ (U : Matrix (Fin (Yc D 0).rank) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D))
      (U' : Matrix (Fin D.R.r) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧
      ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.IndefR.Lev.finE (Yc D 0) (MulAut.conj t (PY.ψ y))).1 =
        HMul.hMul (HMul.hMul U (((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r)
          (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF))) U' := by
  obtain ⟨⟨β, β', h1, h2, hβ⟩, -⟩ := hP
  have hbb := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h1
  have hbb' := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h2
  refine ⟨HMul.hMul (Formalism.IndefR.Lev.finE (Yc D 0) t).1 (β.map (Formalism.IndefR.Lev.swapAE D)),
    HMul.hMul (β'.map (Formalism.IndefR.Lev.swapAE D)) ((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map _), hbb, Matrix.one_mul, Units.mul_inv]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1), Units.inv_mul,
      Matrix.one_mul, hbb']
  · intro y
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    have e1 := finE_val_eq D (Yc D 0) (PY.ψ y)
    have e3 := e1.trans (congrArg (fun M => M.map (Formalism.IndefR.Lev.swapAE D)) (hβ y))
    rw [e3]
    exact conj_map _ _ _ _ _ _ _ (map_cast_swap D hF _)

theorem fmat_iota_conj_stdPsi : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)), StdPsi hF PY → ∃ (U : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) (U' : Matrix (Fin D.R.r) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧ ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ y))).2) = U * ((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF) * U' := by
  intro D hF PY t hP
  obtain ⟨U, U', h1, h2, h3⟩ := finE_conj_stdPsi D hF PY t hP
  exact ⟨U, U', h1, h2, fun y => (fmat_iota D _).trans (h3 y)⟩

end GlobalTheory.FixedConjMat
