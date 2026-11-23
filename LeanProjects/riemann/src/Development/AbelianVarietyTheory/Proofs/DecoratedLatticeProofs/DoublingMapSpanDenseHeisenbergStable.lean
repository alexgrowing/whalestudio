import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsSumUniformLimitProductSpan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNeg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
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

namespace GlobalTheory.Core.Rk.DoubleSpan

variable {D : D7}

theorem span_delta_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A W : HSp D) :
    (Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂} :
      Submodule ℂ (WO (dblSp A) W → ℂ)) =
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨f₁, f₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨f₁, fun x => starRingEnd ℂ (f₂ (-x)), h₁,
      GlobalTheory.CjNeg.theta_negS hψ (GlobalTheory.NegWeil.theta_refl h₂), ?_⟩
    funext x
    exact (GlobalTheory.DoublingTheta.boxS_apply A W f₁ (fun x => starRingEnd ℂ (f₂ (-x))) x).symm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨g₁, g₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨g₁, fun x => starRingEnd ℂ (g₂ (-x)), h₁,
      GlobalTheory.NegWeil.theta_refl (GlobalTheory.CjNeg.theta_negS' hψ h₂), ?_⟩
    funext x
    refine ((GlobalTheory.DoublingTheta.boxS_apply A W g₁ g₂ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, neg_neg, Complex.conj_conj]

theorem prodSpan_theta_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S A B : HSp D}
    (o : GlobalTheory.MixModel.OrthDec S A B) (W : HSp D) :
    (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), IsThetaFunO ψ S W g) ∧
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), ∀ w,
      heisO ψ S W w g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W) := by
  refine ⟨fun g hg => ?_, fun g hg w => ?_⟩
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      exact o.isThetaFunO_boxS hA hB
    | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ S W
    | add a b _ _ ha hb => exact Formalism.IndefR.Fock.CCR.theta_add ha hb
    | smul c a _ ha => exact Formalism.IndefR.Fock.CCR.theta_smul ha c
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hA (o.resS W w).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hB (o.resS W w).2, ?_⟩
      exact o.heisO_boxS ψ W fA fB w
    | zero =>
      have : heisO ψ S W w 0 = 0 := by funext x; simp [heisO]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : heisO ψ S W w (a + b) = heisO ψ S W w a + heisO ψ S W w b := by
        funext x; simp only [heisO, Pi.add_apply]; ring
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : heisO ψ S W w (c • a) = c • heisO ψ S W w a := by
        funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact Submodule.smul_mem _ c ha

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D), IsStdChar D ψ (-1) → let M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂}; (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧ ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := by
  intro D ψ A W hψ M
  have hM : M = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := span_delta_eq hψ A W
  obtain ⟨h1, h2⟩ := prodSpan_theta_heis hψ (GlobalTheory.DoublingTheta.sumDec A (negSp A)) W
  rw [hM]
  exact ⟨h1, h2, fun f hf =>
    GlobalTheory.DenseSum.unifLimit_prodSpan D ψ hψ _ A (negSp A) W (GlobalTheory.DoublingTheta.sumDec A (negSp A)) f hf⟩

end GlobalTheory.Core.Rk.DoubleSpan
