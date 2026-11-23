import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweConditionOfWeil
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRealPlaceCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweConditionOfWeilStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
namespace GlobalTheory.HoweFockReal
theorem howe_condition_action_coinvariants_fock : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  GlobalTheory.RealQuot.HoweCond (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) (GlobalTheory.RealQuot.coinv ε A B eT) := by
  intro hH hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨Xs, Ws, Mo, ψ', χX, χW, om, τ, hcm, hstd, hX, hXd, hWs, hWd, hrX, hrW, hhX, hhW, hwe, hcX, hcW,
    Φ, hinj, hran, hLT, hKT, hLS, hKS⟩ := _root_.GlobalTheory.T.twist_real_place_correspondence hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨⟨L, hL⟩, hsum⟩ := hH D.host.F D.host.E D.sp.cm.sig hcm M.rank X.rank Xs Ws Mo ψ' χX χW om hstd hX hXd hWs hWd
    hrX hrW hhX hhW hwe τ hcX hcW
  have key : ∀ N : Submodule ℂ (PolF D X.rank M.rank),
      GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
      GlobalTheory.RealQuot.coinv ε A B eT ≤ N → GlobalTheory.Published.ThetaSubInf Mo ψ' τ om (N.map Φ) := by
    intro N hs hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hran]
      exact LinearMap.map_le_range
    · intro γ hγ f hf f₁ h
      exact Submodule.map_mono hc (hLS γ hγ f hf f₁ h)
    · intro k hk f hf f₁ h
      exact Submodule.map_mono hc (hKS k hk f hf f₁ h)
    · intro γ hγ f hf f₁ h
      exact hLT N hs γ hγ f hf f₁ h
    · intro k hk f hf f₁ h
      exact hKT N hs k hk f hf f₁ h
  have hne : ∀ N : Submodule ℂ (PolF D X.rank M.rank), N ≠ ⊤ → N.map Φ ≠ Mo.Pol ψ' τ := by
    intro N hN h
    apply hN
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top, hran]
  refine ⟨⟨L, fun m N hN hk => hL m (fun i => (N i).map Φ) ?_ fun i => key _ (hk i).1 (hk i).2⟩, ?_⟩
  · intro i j hij
    exact (Submodule.map_strictMono_of_injective hinj) (hN hij)
  · intro N N' hs hc hN hs' hc' hN' hsup
    apply hsum _ _ (key N hs hc) (key N' hs' hc') (hne N hN) (hne N' hN')
    rw [← Submodule.map_sup, hsup, Submodule.map_top, hran]
end GlobalTheory.HoweFockReal
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  GlobalTheory.RealQuot.HoweCond (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) (GlobalTheory.RealQuot.coinv ε A B eT) := by
  first | exact @_root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock | exact _root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock | (intros; apply _root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock <;> assumption)
end
