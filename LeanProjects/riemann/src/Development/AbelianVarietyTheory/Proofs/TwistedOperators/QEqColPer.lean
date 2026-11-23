import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DblHandEqBiLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingsOfChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OverAllExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem Q_eq_colPer (hM : M.Is t) : ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj))
    (Φ : (chainFrom G Wl t hM σ j hj vN).Data), (chainFrom G Wl t hM σ j hj vN).IsTheta Φ →
    ∀ (F : Fn G (.grid D.R.m D.R.m)), IsContAut _ F → ∀ (φ : GA D (G.V (.top j)) → ℂ), IsContAut _ φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h : (chainFrom G Wl t hM σ j hj vN).Var),
      (chainFrom G Wl t hM σ j hj vN).Q Φ F φ g h = colPer Wl hM σ j hj vN Φ F φ g h
  | 0, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, _ => LastSeeSawStep.main G Wl t hM j hj vN Φ.1 Φ.2 F φ hΦ.1 hΦ.2 hF hφ g
  | σ + 1, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, h => by
    have ih := Q_eq_colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 hΦ.2.2 F hF
    let B := besAt G hM j (σ + 1) hj vN
    let J := jacAt G hM (j + 1) (σ + 1) (by omega)
    let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
    let s₁ : StepBF Wl.ψ B J :=
      stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
    let s₂ : StepFB Wl.ψ J B' :=
      stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
    have t₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h.1) Φ.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h.1) _ hΦ.1)
    have t₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h.1, h.2.1) Φ.2.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).2 _ J B' s₂ _ (s₂.weil.om_pres (h.1, h.2.1) _ hΦ.2.1)
    have hc := GlobalTheory.FinPl.ValDbl.contAut_hand0 s₁ s₂ (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) hφ t₁ t₂
    have e := ih _ hc h.2.1 h.2.2
    refine e.trans ?_
    show colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2 = colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2
    congr 1
    exact dbl_hand_eq_biLift G Wl t hM σ j hj vN Φ.1 Φ.2.1 φ hΦ.1 hΦ.2.1 hφ g h.1 h.2.1

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem iter_chain (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter ((chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := (GlobalTheory.Unf.unfoldings_of_chain D).2.2.2.2.2.1 Wl.ψ _ _ _ (chain G Wl t hM) (chainData G Wl t hM d) F φ 1
    (chainData_isTheta G Wl t hM d hd) hF hφ hR
  have e : rTrans 1 ((chain G Wl t hM).down (chainData G Wl t hM d) F) = (chain G Wl t hM).down (chainData G Wl t hM d) F := by
    funext z; simp [rTrans]
  rwa [e] at h

theorem chain_Q_eq (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ) (h' : (chain G Wl t hM).Var) :
    (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 h' =
      colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 h' :=
  Q_eq_colPer Wl hM _ 0 top_idx (topVN hM) _ (chainData_isTheta G Wl t hM d hd) F hF φ hφ 1 h'

theorem iter_colPer (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter (colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := iter_chain Wl hM d hd F hF φ hφ hR
  have e : (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 = colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 :=
    funext (chain_Q_eq Wl hM d hd F hF φ hφ)
  rwa [e] at h

end GlobalTheory.RowChain
