import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PinCovCarrierInTc

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem pinCov_ccOne (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (u u' : D.what₂.Word) (e : NumberField.InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j))
    (hTT : HypTT D u u')
    (hW : ∀ j, GoodW D (e (plE D j)) u u' θ (locW C u u' (e (plE D j))))
    (hA : ∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j))))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1)
    (hscl : ∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) (hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j)
      (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ'
      (fun j => ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀)))
    (Ac : ℝ) (hAc : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ Ac)
    (hCC : ∀ j, Formalism.FourierDecayAlt.B.InCC Ac 1 (fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j)
      (ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)))) :
    JointPin.PinCov (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ'
      (fun j => ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀) Mo) := by
  refine pinCov_carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo ?_
  intro j γ μRv ν hH
  have hP := pinHyp_at X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo j γ μRv ν hH
  exact pinAt_one C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j)
    (hscl j) (hcO j) Ac hAc (hCC j) γ μRv ν hP

end Formalism.L2.SG.Pf.Carrier.CarPinTor
