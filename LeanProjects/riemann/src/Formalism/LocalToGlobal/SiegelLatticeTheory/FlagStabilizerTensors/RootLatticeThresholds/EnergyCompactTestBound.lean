import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJointAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyNF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeZhatTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNormSt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstA
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GridsRichITc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoef

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem energy_compact_test_bound {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) {θ : ℝ} (C : Choice T.X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie T.X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j)) (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j))
    (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)) (cc : Fin (nfE D) → ℂ)
    (i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (T.X.Vloc u (tauE T.X e j)) (T.X.Vloc u' (tauE T.X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf T.X C u u' e j).base.π
      (towersOf T.X C u u' e j).base.z (m0E T.X C u u' e j *ᵥ nuE T.X C u' e i0' j)) (A₀ : ℝ)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd Cb Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0b i0b' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
    (hpin : JointPin.PinCov (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))))
    (hBuilt : Formalism.FourierDecayAlt.D.IsBuilt (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE T.X C u' e i0') (m0E T.X C u u' e) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀) :
    (∏ v, (Formalism.FourierDecayAlt.B.normSq ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v)).toReal /
        Formalism.FourierDecayAlt.D.GamLev (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r (Formalism.FourierDecayAlt.D.kapG (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.D.deG (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0) =
      (Formalism.L2.SG.SpectralTiesReal.massDataY T.X T.hb T.Y u u' X0 T.ψ sd Cb Th vR Q i0b i0b' νq).IntN := by
  have hFX : (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).FromX :=
    BaseOf.fromX T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
      (nuE T.X C u' e i0') (m0E T.X C u u' e) (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hg0 : 0 < (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.g := by
    show 0 < D.host.g 0 * D.host.g 1
    exact Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  have hZ := zhatTr_carrierOf T.X u u' e he hv C CA de de' l (gridT e l) (grid1T e l) (towersOf T.X C u u' e)
    (Tz_towersOf_base_eq_T T.X C u u' e) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) (nuE T.X C u' e i0') (m0E T.X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hPN := JointPin.placeNormG_of_pin (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl hpin
    (JointPinNormSt.normBridge_of_zhat _ rfl hZ) hFX hBuilt hg0
  have hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE Formalism.FourierDecayAlt.S6.rd
    rw [Int.cast_abs, one_div]
  have hk1 : 1 ≤ (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.G.k := by
    show 1 ≤ D.R.k
    have := Formalism.MainNotions.BridgeLemma.five_le_k D
    omega
  exact EnergyNF.energy_norm_bound_third_form T.hb T.Y X0 T.ψ sd Cb Th vR Q i0b i0b' νq (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl rfl
    (fun v => Tz_towersOf_base_eq_T T.X C u u' e _) rfl hrd hg0 hk1 (Formalism.L2.SG.WConst.card_places T.X) T.ψ_char T.ψ_std
    (Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds T u u') (Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds T.X u u' T.ψ) hPN

end Formalism.L2.SG.Pf.CarrierXAll
