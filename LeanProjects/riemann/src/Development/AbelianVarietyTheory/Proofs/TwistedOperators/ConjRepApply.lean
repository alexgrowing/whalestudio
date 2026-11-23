import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

def conjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep S T :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd (Equiv.refl (WO S T))).comp ω

theorem conjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    conjRep ω p F = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (ω p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F)) := rfl

def adjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep T S :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint (conjRep ω)

theorem adjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (h : GA D T) (g : GA D S) (F : WO T S → ℂ) :
    adjRep ω (h, g) F = fun y => ω (g, h) (fun x => F (adjO T S x)) (adjO S T y) := by
  funext y
  show starRingEnd ℂ (starRingEnd ℂ (ω (g, h) (fun x => starRingEnd ℂ (starRingEnd ℂ (F (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x))))
    (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S y))) = _
  simp only [Complex.conj_conj, GlobalTheory.ConjAdjWeil.dagger_eq]

open GlobalTheory.FockAdjoint in

def swapHom {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank →ₐ[ℂ] PolF D S.rank T.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)

open GlobalTheory.FockAdjoint in

def swapInv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D S.rank T.rank →ₐ[ℂ] PolF D T.rank S.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1)

open GlobalTheory.FockAdjoint in
theorem swapHom_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D T.rank S.rank) :
    swapHom A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapHom]

open GlobalTheory.FockAdjoint in
theorem swapInv_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D S.rank T.rank) :
    swapInv A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapInv]

open GlobalTheory.FockAdjoint in

def swapEquiv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank ≃ₐ[ℂ] PolF D S.rank T.rank :=
  AlgEquiv.ofAlgHom (swapHom A B) (swapInv A B)
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapInv_X, map_mul, swapHom_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapHom_X, map_mul, swapInv_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])

example {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    conjRep (conjRep ω) p F = ω p F := by
  rw [conjRep_apply, conjRep_apply, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj id id (fun _ => rfl), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj id id (fun _ => rfl)]

end GlobalTheory.AdjTr

end
