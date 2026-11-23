import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFiniteDatumIsSchwartzBruhatHalfStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelationsStatement
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

open Classical

namespace GlobalTheory.Core.Rk.Exh.SmallSupp

theorem selfDual_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem wcoef_eq_zero_off_prin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  intro D ψ θ A H χA om sA sH _hθ _hη hW _hcA _hcH hrank β Z hP βH f₀ f hβH hvec hthf ν 𝓕 hν g hg hnot
  have sdA := selfDual_frameLat A
  have sdH := selfDual_frameLat H
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  have hQ : (prinDat A Z).Q = ∅ := rfl
  have hPg : (prinDat A Z).Pg = Z := rfl
  have hint : ∀ v, (∀ PP ∈ (prinDat A Z).Pg, PP.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig A.gram (frameLat A) v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [under, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D A H (frameLat A) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1) e sdA hP.frame hrank hQ he g hint x hx h)
  have hsb := GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half D A H (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1)
    ((prinDat A Z).Pg ∪ ∅) e sdA sdH hP.frame hβH he
  obtain ⟨n, a, y, -, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D ψ A H hW.std (frameLat A) (frameLat H) sdA sdH
    ((prinDat A Z).Pg ∪ ∅) e he f₀ _ f hsb hth g hsupp
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D ψ A H χA 1 om hW ν 𝓕 hν f hthf g n a y h1 h2

end GlobalTheory.Core.Rk.Exh.SmallSupp
