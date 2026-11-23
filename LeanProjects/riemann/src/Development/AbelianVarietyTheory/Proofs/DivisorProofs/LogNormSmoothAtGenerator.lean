import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLineBundleInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAdelicMetricDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetricLocalPotentialExists
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.LnNSmooth

theorem cInfAt_lnN : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (Δ : Y.Dv) (m : (cxSt F).Met Y σ Δ), (cxSt F).mSmooth Y σ Δ m → ∀ (f : Y.Fn) (z0 : Pts Y σ), Δ.GeneratesAt (under z0) f → CInfAt (fun z => lnN m f z) z0 := by
  intro F _ _ Y σ Δ m h f z0 hf
  have hp := presents_toLB Δ
  have hpos := Var.mSmooth.posSet_eq h
  set ψ := Var.Met.toWeight m hpos hp
  have hψ : ψ.IsCInf := (Weight.isCInf_iff_isSmooth (Y.an σ)).2 (Var.mSmooth.isSmooth_toWeight h hp)
  have hpn := Var.pn_ofWeight_toWeight hpos hp
  obtain ⟨c, hc⟩ := exists_chart (isLB_toLB Δ) (under z0)
  obtain ⟨U, hU, hUg⟩ := GlobalTheory.CombPot.generatesAt_exists_nhds hf
  set W : Y.X.Opens := U ⊓ (toLB Δ).U c
  have hzW : z0 ∈ ptsIn Y.str σ W := mem_ptsIn.2 ⟨hU, hc⟩
  have hloc : ∀ w ∈ ptsIn Y.str σ W, lnN m f w =
      (1 / 2) * Real.log (‖ratVal (f * (c.1.2 : Y.Fn)) w‖ ^ 2) + (1 / 2) * (-ψ.φ c w) := by
    intro w hw
    have hw' := mem_ptsIn.1 hw
    have hgen : Δ.GeneratesAt (under w) f := hUg _ hw'.1
    have hu : UnitAt (under w) (f * (c.1.2 : Y.Fn)) := (hp.isEqn c _ hw'.2).generatesAt_iff.1 hgen
    have eP : (cxSt F).pn Y σ Δ m ((cxSt F).cx Y σ f) w =
        ‖ratVal (f * (c.1.2 : Y.Fn)) w‖ ^ 2 * Real.exp (-ψ.φ c w) :=
      (congrFun (congrFun hpn _) _).symm.trans ((cxSt F).pn_ofWeight Y σ Δ _ _ hp ψ _ w c hw'.2 hgen.regularAt)
    have hA : ratVal (f * (c.1.2 : Y.Fn)) w ≠ 0 := ratVal_ne_zero hu
    simp only [lnN]
    rw [eP, Real.log_mul (pow_pos (norm_pos_iff.2 hA) 2).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hu0 : UnitAt (under z0) (f * (c.1.2 : Y.Fn)) := (hp.isEqn c _ hc).generatesAt_iff.1 hf
  have hψc : CInfAt (ψ.φ c) z0 := hψ c _ (mem_ptsIn.2 hc)
  refine (((MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_log_normSq_ratVal hu0).const_mul (1 / 2)).add
    (hψc.neg.const_mul (1 / 2))).congr ?_
  filter_upwards [(isOpen_ptsIn W).mem_nhds hzW] with w hw using hloc w hw

end GlobalTheory.Mean4O.LnNSmooth
