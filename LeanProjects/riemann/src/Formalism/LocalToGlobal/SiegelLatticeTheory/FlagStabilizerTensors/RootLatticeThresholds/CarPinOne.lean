import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTPinWrap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CutAtHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTAmpVec

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

def ccOne (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) : ℂ :=
  lamPl (cOf hB u τ) (sclOf hB u u' τ)
    (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
    (muN_eq_haarLie D.R.k D.R.rS).choose

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ccOne_ne (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) :
    ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := (muN_eq_haarLie D.R.k D.R.rS).choose_spec
  exact lamPl_ne _ _ _ D θ _ hcO hscl
    (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec.1 h0 h1
    (Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem pinAt_one (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) (A₀ : ℝ)
    (hA₀ : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1
      (fcAt C u u' τ a b ξ ξ' (ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)))
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hP : PinHypAt C u u' τ γ μRv ν) :
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
      Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) =
      Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)))
        (fcAt C u u' τ a b ξ ξ' (ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)) := by
  set cc := ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl with hcc
  have hc0 : cc ≠ 0 := ccOne_ne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl hcO
  have hκ := (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec
  obtain ⟨h0, h1, hN⟩ := (muN_eq_haarLie D.R.k D.R.rS).choose_spec
  have hCut := cutAt_holds C u u' τ a b ξ ξ' cc A₀ hA₀ hCC
  obtain ⟨hGv, hMono, hRel, hH, hQ⟩ := id hP
  have hLz := (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz
  have hLz' := (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz'
  have hWc := muWc_eq C u τ hLz.1 hLz.2
  have hWc' := muWc_eq C u' τ hLz'.1 hLz'.2
  have hH' := haarTr_holds C u u' τ γ μRv hH
  obtain ⟨νB, hq⟩ := orbQuot_exists (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
    (gB_mem C u τ γ) hH'
  have hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData
      (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB :=
    ⟨gB_mem C u τ γ, gf_B C u u' τ γ hGv, mono_B C u u' τ γ hMono,
      relStab_of_relevant C hB u u' τ hW hA hT hT' γ hRel, hH', hq, quotTr_holds C u u' τ γ μRv ν hH hQ⟩
  have hpinAt := pinAt C hB u u' τ hW hA hT hT' a b ξ ξ' cc hc0 _ hκ.1 hκ.2 _ h0 h1 hN hWc hWc' hcO hscl γ μRv ν νB
    hcell (Formalism.L2.SG.Pf.LocJEq.integrand_aesm C hB u u' τ γ ν) (hCut γ μRv ν hP)
  rw [hpinAt]
  have e : lamPl (cOf hB u τ) (sclOf hB u u' τ)
      (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
      (muN_eq_haarLie D.R.k D.R.rS).choose * cc⁻¹ = 1 := by
    rw [hcc]; exact mul_inv_cancel₀ hc0
  rw [e, one_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
