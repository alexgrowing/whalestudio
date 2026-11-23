import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RatFinIso

variable {D : D7}

theorem symplOH_ratW_finRat_neg (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 := by
  set u : WO S T := ratW T S v - GlobalTheory.VacUnique.finRat S T v with hu
  have hfin : u.map (finPart D) = 0 := by
    funext i j
    have e1 := congrFun (congrFun (GlobalTheory.VacUnique.finRat_fin S T v) i) j
    show finPart D (ratW T S v i j - GlobalTheory.VacUnique.finRat S T v i j) = 0
    rw [RingHom.map_sub]
    simp only [Matrix.map_apply] at e1
    rw [e1, sub_self]
  have hr : ratW T S v = u + GlobalTheory.VacUnique.finRat S T v := by rw [hu, sub_add_cancel]
  rw [hr, GlobalTheory.FinTranslate.symplOH_add_left, map_neg, GlobalTheory.FinTranslate.symplOH_neg_right,
    GlobalTheory.FinTranslate.symplOH_neg_right, GlobalTheory.FinTranslate.symplOH_self,
    GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T v) hfin]
  simp

theorem isotropic : ∀ {D : D7} (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 :=
  fun S T v => symplOH_ratW_finRat_neg S T v

end GlobalTheory.RatFinIso

end
