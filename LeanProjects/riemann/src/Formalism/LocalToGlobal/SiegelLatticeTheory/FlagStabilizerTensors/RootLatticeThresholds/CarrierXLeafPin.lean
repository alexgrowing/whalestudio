import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinOneCov
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefCCT

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem xLeafAt_of_pins {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)
    (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (sc : ℝ) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn : ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j))
    (hTT : HypTT D u u')
    (hW : ∀ j, GoodW D (e (plE D j)) u u' θ (locW C u u' (e (plE D j))))
    (hA : ∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j))))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1)
    (hscl : ∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) (hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0)
    (h : Fin (nfE D) → ℝ) (hlam : ∀ j, Formalism.QuantumDeterminants.IsHCParam (lamD D (e (plE D j))))
    (hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (h j))
    (hok : ∀ j, Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (h j))
    (Ac : ℝ) (hAc : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ Ac)
    (hAc0 : 0 ≤ Ac) (hAch : ∀ j, Ac ≤ h j / 2)
    (cc : Fin (nfE D) → ℂ)
    (hcc : cc = fun j => Formalism.L2.SG.Pf.Carrier.CarPinTor.ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
      hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) :
    XLeafAt X C u u' e he hv CA de de' l i0 i0' sc FdN FdN' νq jn a b ξ ξ' cc := by
  subst hcc
  refine ⟨fun j => (hpin1 j).1, fun j => (hpin1 j).2.1, fun Θ TP A₀ => ?_⟩
  exact Formalism.L2.SG.Pf.Carrier.CarPinTor.pinCov_ccOne C hB hJ large₂ hCl hH0 u u' e he hv CA de de' l (gridT e l) (grid1T e l)
    a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ (modelsOf _) Ac hAc
    (fun j => Formalism.L2.SG.Pf.CoefCCT.fcT_inCC C e u u' a b ξ ξ'
      (fun j => Formalism.L2.SG.Pf.Carrier.CarPinTor.ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
        hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) h hlam hgap hok hAc0 hAch (fun j => (hpin1 j).1) (fun j => (hpin1 j).2.1) j 1)

end Formalism.L2.SG.Pf.CarrierXAll
