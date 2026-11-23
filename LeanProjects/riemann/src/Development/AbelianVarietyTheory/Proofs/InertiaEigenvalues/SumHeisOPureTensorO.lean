import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FiniteHeisComb

variable {D : D7}

theorem heisO_aPlus (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (aPlus (heisO ψ S T) θ τ J z g) = aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  simp only [aPlus, crea]
  change GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u _ = _
  rw [map_smul, map_sub, map_smul]
  show _ • (heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
  rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu]

theorem aPlus_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : WO S T → ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (s : Finset (WO S T)) :
    IsThetaFunO ψ S T (∑ u ∈ s, c u • heisO ψ S T u g) ∧
      aPlus (heisO ψ S T) θ τ J z (∑ u ∈ s, c u • heisO ψ S T u g) =
        ∑ u ∈ s, c u • aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (GlobalTheory.OrientedHeis.theta_zero : IsThetaFunO ψ S T 0), ?_⟩
    have e := GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := S) (T := T))
    simpa using e
  | insert a s ha ih =>
    have ht : IsThetaFunO ψ S T (c a • heisO ψ S T a g) :=
      GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨GlobalTheory.OrientedHeis.theta_add ht ih.1, ?_⟩
    rw [GlobalTheory.AdTh.SourceBasis.aPlus_add hψ hθ τ J z ht ih.1, ih.2,
      GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)]

theorem sum_heisO_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ x : WO S T → ℂ, IsThetaFunO ψ S T x → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, (c.sum fun u z => z • heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P)) = pureTensorO ψ θ S T sS sT BS BT (c.sum fun u z => z • heisO ψ S T u x) P := by
  intro D ψ θ S T hψ hθ sS BS sT BT c hc x hx P
  let Φ : Module.End ℂ (WO S T → ℂ) := c.sum fun u z => z • GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u
  have hΦ : ∀ g, Φ g = c.sum fun u z => z • heisO ψ S T u g := by
    intro g
    simp only [Φ, Finsupp.sum]
    rw [LinearMap.sum_apply]
    rfl
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ ha hb => GlobalTheory.OrientedHeis.theta_add ha hb) (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) Φ
    (fun k g hg => ⟨?_, ?_⟩) x hx P).2
  · rw [hΦ, hΦ] at h
    exact h
  · exact GlobalTheory.AdTh.SourceBasis.aPlus_th hψ hθ _ _ _ hg
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll]
    rw [hΦ, hΦ, Finsupp.sum, Finsupp.sum, (aPlus_sum hψ hθ τ _ _ c hg c.support).2]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [heisO_aPlus ψ hθ (hc u hu)]

end GlobalTheory.FiniteHeisComb
