import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSConclusion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXVIndepP
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsCC
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSFinalP
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsGV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDenseMain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhsWLimOfLeaves
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CarrierNeedsFromD

set_option linter.unusedVariables false

noncomputable section

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierT

open MeasureTheory Matrix
open scoped InnerProductSpace

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf

namespace GlobalTheory.CarrierGap
theorem ampVec_genG (hJ : CompanionTheory.Lime.BM.UniqGap) (hI : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs) (hAt : CompanionTheory.Lime.BM.AtFormAdmOne) (hAKF : Formalism.MainNotions.S.Pv.AmpDD.BM.AmpKF)
    (hCC : Formalism.MainNotions.S.Pv.AmpDD.CellConv) {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 Cn : ℝ}
    (hGap : Formalism.MainNotions.S.Pv.AmpDD.GapOfHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hNV : Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hTT : HypTT D w w')
    (θ : ℝ) (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (A : LocS W) (hA : GoodS D lam' A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') (a b : A.H) (ξ : W.Wp) (ξ' : W.Wq)
    (hka : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ a)
    (hkb : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ b)
    (hn : ⟪A.B a, ξ⟫_ℂ * ⟪ξ', A.B' b⟫_ℂ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG γ μR νR ν →
      OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT')
        (Formalism.MainNotions.S.Pv.AmpDD.coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') a b ξ ξ') γ ν = κ • A.J νR γ := by
  obtain ⟨h, hg, hok, hcell⟩ := hGap hH τ lam' hl
  set L := toBessel D τ w w' θ W lam' A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := Formalism.L2.SG.AmpOrbPf.BM.ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    hNV hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp
  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩
  have has : a ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 a hka
  have hbs : b ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 b hkb
  have hBa : A.B a = c0 • l a := hc0 a has
  have hBb : A.B' b = c0' • l' b := hc0' b hbs
  rw [hBa, hBb, inner_smul_left, inner_smul_right] at hn
  have hc0ne : c0 ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  have hc0ne' : c0' ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  set s : ℂ := ⟪l a, ξ⟫_ℂ * ⟪ξ', l' b⟫_ℂ with hs
  have hs0 : s ≠ 0 := by
    intro h0; apply hn
    have : (starRingEnd ℂ) c0 * ⟪l a, ξ⟫_ℂ * (c0' * ⟪ξ', l' b⟫_ℂ) = (starRingEnd ℂ) c0 * c0' * s := by
      rw [hs]; ring
    rw [this, h0, mul_zero]
  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0ne : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hA.2.2.2.2.1
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'
  have ht0 : t ≠ 0 := by
    rw [ht]; exact_mod_cast (norm_ne_zero_iff.mpr hv0ne)
  have hcN : (A.cN : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hA.2.2.2.2.2.2.2.1)
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  have hK10 : K1 ≠ 0 := by
    rw [hK1]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero hcN) (mul_ne_zero hc0ne ht0)) ?_
    exact (map_ne_zero _).mpr (mul_ne_zero hc0ne' ht0)
  have hw1 : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0ne)
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  have hdg0 : dg ≠ 0 := by
    rw [hdg]
    exact_mod_cast (ne_of_gt (Formalism.L2.S.Pv.AmpOrbCoef.fdegH_pos hA.1 hA.2.1 hG hw1))
  refine ⟨dg * s * K1⁻¹, mul_ne_zero (mul_ne_zero hdg0 hs0) (inv_ne_zero hK10), ?_⟩
  intro γ μR νR ν hCD
  obtain ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩ := hCD
  have hCD' : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨bb, hb0, hbm, hbi⟩ := hCC _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD' hMono
  have hAmp := hAKF hI _ _ L h W.μG w0 l l' hOP γ μR νR ν hCD' bb hb0 hbm hbi a b hka hkb ξ ξ'
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae
  have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν := hAmp
  have e1 : OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν =
      dg • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
    rw [hAmp']; exact (smul_inv_smul₀ hdg0 _).symm
  have e2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ = K1⁻¹ • A.J νR γ := by
    rw [hJ1, smul_smul, inv_mul_cancel₀ hK10, one_smul]
  rw [e1, e2]
  simp only [smul_smul, mul_assoc]
  rfl

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ampVec_carrierG (hJ : CompanionTheory.Lime.BM.UniqGap) {D : D7} (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} {C : Formalism.L2.SG.LocWSOf.Choice X θ} (hB : Formalism.L2.SG.LocWSOf.WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hTT : HypTT D u u')
    (hW : GoodW D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ))
    (hA : GoodS D (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)) (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (a b : X.B.H (Formalism.L2.SG.LocWSOf.vOf X τ)) (ξ : X.Vloc u (Formalism.L2.SG.LocWSOf.vOf X τ))
    (ξ' : X.Vloc u' (Formalism.L2.SG.LocWSOf.vOf X τ)) (c : ℂ) (hpin : CoefPin hB u u' τ a b ξ ξ' c)
    (hscl : Formalism.L2.SG.LocWSOf.sclOf hB u u' τ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ)
        (Formalism.L2.SG.LocWSOf.locS hB u u' τ) hW hA hT hT') (Formalism.L2.SG.LocWSOf.locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)
          hW hA hT hT')
        (Formalism.MainNotions.S.Pv.BetaCut.coefM (Formalism.L2.SG.LocWSOf.sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') γ ν =
        κ • (Formalism.L2.SG.LocWSOf.locS hB u u' τ).J νR γ := by
  obtain ⟨hka, hkb, hn1, -⟩ := hpin
  have hn : ⟪(Formalism.L2.SG.LocWSOf.locS hB u u' τ).B a, ξ⟫_ℂ * ⟪ξ', (Formalism.L2.SG.LocWSOf.locS hB u u' τ).B' b⟫_ℂ ≠ 0 := by
    show ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
      ⟪ξ', Formalism.L2.SG.LocWSOf.sclOf hB u u' τ • Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ ≠ 0
    rw [inner_smul_right]
    have e : ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
        (Formalism.L2.SG.LocWSOf.sclOf hB u u' τ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) =
        Formalism.L2.SG.LocWSOf.sclOf hB u u' τ *
          (⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) := by ring
    rw [e, hn1, mul_one]
    exact hscl
  have hl : l1dist (lamD D τ) (lamD D τ) ≤ (0 : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
    simp [l1dist]
  exact ampVec_genG hJ CompanionTheory.Lime.BM.inputs (CompanionTheory.Lime.BM.atFormAdmOne hJ)
    Formalism.MainNotions.S.Pv.AmpDDPf.BM.amplitude_K_finite Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
    (Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 hCl (by linarith))
    (Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith)) hH τ u u' hTT θ _ hW (lamD D τ) hl _ hA
    hT hT' a b ξ ξ' hka hkb hn

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.CarPinTor

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

namespace GlobalTheory.CarrierGap
open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
def ccOneG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) : ℂ :=
  lamPl (cOf hB u τ) (sclOf hB u u' τ)
    (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
    (muN_eq_haarLie D.R.k D.R.rS).choose

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ccOne_neG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) :
    ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := (muN_eq_haarLie D.R.k D.R.rS).choose_spec
  exact lamPl_ne _ _ _ D θ _ hcO hscl
    (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec.1 h0 h1
    (Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem pinAt_oneG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) (A₀ : ℝ)
    (hA₀ : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1
      (fcAt C u u' τ a b ξ ξ' (ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)))
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hP : PinHypAt C u u' τ γ μRv ν) :
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
      Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) =
      Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)))
        (fcAt C u u' τ a b ξ ξ' (ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)) := by
  set cc := ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl with hcc
  have hc0 : cc ≠ 0 := ccOne_neG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl hcO
  have hκ := (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec
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
      (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
      (muN_eq_haarLie D.R.k D.R.rS).choose * cc⁻¹ = 1 := by
    rw [hcc]; exact mul_inv_cancel₀ hc0
  rw [e, one_smul]

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.CarPinTor

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

namespace GlobalTheory.CarrierGap
open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem pinCov_ccOneG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
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
      (fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀)))
    (Ac : ℝ) (hAc : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ Ac)
    (hCC : ∀ j, Formalism.FourierDecayAlt.B.InCC Ac 1 (fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j)
      (ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)))) :
    JointPin.PinCov (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ'
      (fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀) Mo) := by
  refine pinCov_carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo ?_
  intro j γ μRv ν hH
  have hP := pinHyp_at X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo j γ μRv ν hH
  exact pinAt_oneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j)
    (hscl j) (hcO j) Ac hAc (hCC j) γ μRv ν hP

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierXAll

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CarrierGap
set_option maxHeartbeats 4000000 in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem xLeafAt_of_pinsG {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)
    (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
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
    (hcc : cc = fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
      hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) :
    XLeafAt X C u u' e he hv CA de de' l i0 i0' sc FdN FdN' νq jn a b ξ ξ' cc := by
  subst hcc
  refine ⟨fun j => (hpin1 j).1, fun j => (hpin1 j).2.1, fun Θ TP A₀ => ?_⟩
  exact pinCov_ccOneG C hB hJ large₂ hCl hH0 u u' e he hv CA de de' l (gridT e l) (grid1T e l)
    a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ (modelsOf _) Ac hAc
    (fun j => Formalism.L2.SG.Pf.CoefCCT.fcT_inCC C e u u' a b ξ ξ'
      (fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
        hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) h hlam hgap hok hAc0 hAch (fun j => (hpin1 j).1) (fun j => (hpin1 j).2.1) j 1)

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierXAll

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix InnerProductSpace

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

namespace GlobalTheory.CarrierGap
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem xLeavesP_of_pinsPG (hJ : CompanionTheory.Lime.BM.UniqGap) (hP : XPinsP) : XLeavesP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hne hcb hcT hTies hC' hClp
    hk18 hH0 hPl hSz hi hPt hNu
  obtain ⟨θ, Ch, hB, a, b, ξ, ξ', hTT, hT, hT', hW, hA, hpin1, hscl, hcO⟩ :=
    hP CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18 hH0 hPl hSz
      hi hPt hNu
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hS0 := hH0.1
  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hcn
    push Not at hcn
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hfR 5
    norm_num at this; linarith
  have hrr : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by omega
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by omega) hn1801) ?_
    rw [hrr]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAch := le_of_le_of_eq (ac_le (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose) Cl L.sc.L D.R.rS D.R.k D.R.f hClp hf hL) (by rw [hrr])
  refine ⟨θ, Ch, a, b, ξ, ξ', fun j => ccOneG Ch hB hJ L hCl hH0 u u' (e (plE D j)) hTT (hW j)
    (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j), ?_⟩
  exact xLeafAt_of_pinsG T.X Ch hB hJ L hCl hH0 u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u')
    (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO
    (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) (fun j => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
    (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) _ (le_max_left _ _) (le_max_right _ _) (fun _ => hAch) _ rfl

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem xPinsP_ofG (hJ : CompanionTheory.Lime.BM.UniqGap) (hNZ : KFinNZ) : XPinsP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18
    hH0 hPl hSz hi hPt hNu
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH0.1 (by linarith) hC'
  obtain ⟨Ch⟩ := Formalism.L2.SG.Pf.choiceExists T.X 1 one_pos
  have hB : WuBessel Ch := Formalism.L2.SG.Pf.wuBesselOfLoc_all Ch hG Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds (Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch) (fun τ => Formalism.L2.SG.Pf.dsTr Ch τ) (fun τ => Formalism.L2.SG.Pf.haarTr Ch τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr Ch u τ)
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch
  have hc : ∀ (w : D.what₂.Word) (t : D.what₂.Tau), 0 < cOf hB w t := fun w t =>
    Formalism.L2.SG.Pf.AmpWin.cOf_pos hB (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).1 (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).2
  have hscl : ∀ t, sclOf hB u u' t ≠ 0 := by
    intro t
    have h1 := Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB u' t
    have hl : 0 < (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := ENNReal.toReal_pos h1.1 h1.2.ne
    have hd : 0 < Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))) with h | h
      · exfalso
        have : Subsingleton (T.X.Vloc u' (vOf T.X t)) := Module.finrank_zero_iff.1 h
        apply h1.1
        unfold l2SG
        simp [Subsingleton.elim (phiOf hB u' t _) 0]
      · exact h
    unfold sclOf
    have hpos : 0 < cOf hB u t * (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) : ℝ) /
        (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := div_pos (mul_pos (hc u t) (by exact_mod_cast hd)) hl
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have ha : ∀ j : Fin (nfE D), ∃ a : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) a ∧
      bOf hB u (e (plE D j)) a ≠ 0 := fun j => hNZ D T.X 1 Ch hB u (e (plE D j)) hG
  have hb : ∀ j : Fin (nfE D), ∃ b : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) b ∧
      bOf hB u' (e (plE D j)) b ≠ 0 := fun j => hNZ D T.X 1 Ch hB u' (e (plE D j)) hG
  choose a ha using ha
  choose b hb using hb
  refine ⟨1, Ch, hB, a, b, fun j => (((‖bOf hB u (e (plE D j)) (a j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u (e (plE D j)) (a j),
    fun j => (((‖bOf hB u' (e (plE D j)) (b j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u' (e (plE D j)) (b j),
    Formalism.MainNotions.SchurRelationsDiscreteSeries.hypTT_all u u', Nat.cast_pos.2 (D.mem u).A.T_prime.pos, Nat.cast_pos.2 (D.mem u').A.T_prime.pos,
    fun j => Formalism.L2.SG.Pf.AmpWinRX.goodW_all Ch u u' (e (plE D j)),
    fun j => goodS_of hB u u' (e (plE D j)) (Formalism.L2.SG.Pf.goodSRest_all hG hTies.dsig_tie hB u u' (e (plE D j))),
    fun j => ⟨(ha j).1, (hb j).1, ?_, one_ne_zero⟩, fun j => hscl _, fun j => (hc u _).ne'⟩
  rw [inner_normalize_right (ha j).2, inner_normalize_left (hb j).2, one_mul]

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierXAll

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix InnerProductSpace

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

namespace GlobalTheory.CarrierGap
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem vIndepAtAllP_ofG (hJ : CompanionTheory.Lime.BM.UniqGap) (hNZ : KFinNZ) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.VIndepAtAllP := by
  intro Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨29, 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose|, ?_⟩
  intro C' Cl hC' hClp D L T u u' i0 i0' νq hTies hne hSt hCT hi hNu hPt hH0
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hS0 := hH0.1
  have hk18 := rootLatticeThresholds_k_of_fact hS0 hC'
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hS0 (by linarith) hC'
  obtain ⟨Ch⟩ := Formalism.L2.SG.Pf.choiceExists T.X 1 one_pos
  have hB : WuBessel Ch := Formalism.L2.SG.Pf.wuBesselOfLoc_all Ch hG Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds (Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch) (fun τ => Formalism.L2.SG.Pf.dsTr Ch τ) (fun τ => Formalism.L2.SG.Pf.haarTr Ch τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr Ch u τ)
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch
  set e : InfinitePlace D.host.E ≃ D.what₂.Tau := (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm with he_def
  have he : PlaceTie T.X e := fun x => Formalism.L2.SG.Pf.Carrier.placeTie_ePl T.X x
  have hc : ∀ (w : D.what₂.Word) (t : D.what₂.Tau), 0 < cOf hB w t := fun w t =>
    Formalism.L2.SG.Pf.AmpWin.cOf_pos hB (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).1 (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).2
  have hscl : ∀ t, sclOf hB u u' t ≠ 0 := by
    intro t
    have h1 := Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB u' t
    have hl : 0 < (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := ENNReal.toReal_pos h1.1 h1.2.ne
    have hd : 0 < Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))) with h | h
      · exfalso
        have : Subsingleton (T.X.Vloc u' (vOf T.X t)) := Module.finrank_zero_iff.1 h
        apply h1.1
        unfold l2SG
        simp [Subsingleton.elim (phiOf hB u' t _) 0]
      · exact h
    unfold sclOf
    have hpos : 0 < cOf hB u t * (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) : ℝ) /
        (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := div_pos (mul_pos (hc u t) (by exact_mod_cast hd)) hl
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have ha : ∀ j : Fin (nfE D), ∃ a : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) a ∧
      bOf hB u (e (plE D j)) a ≠ 0 := fun j => hNZ D T.X 1 Ch hB u (e (plE D j)) hG
  have hb : ∀ j : Fin (nfE D), ∃ b : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) b ∧
      bOf hB u' (e (plE D j)) b ≠ 0 := fun j => hNZ D T.X 1 Ch hB u' (e (plE D j)) hG
  choose a ha using ha
  choose b hb using hb
  set ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j) :=
    fun j => (((‖bOf hB u (e (plE D j)) (a j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u (e (plE D j)) (a j) with hξ
  set ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j) :=
    fun j => (((‖bOf hB u' (e (plE D j)) (b j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u' (e (plE D j)) (b j) with hξ'
  have hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1 := fun j =>
    ⟨(ha j).1, (hb j).1, by rw [hξ, hξ']; simp only []; rw [inner_normalize_right (ha j).2, inner_normalize_left (hb j).2, one_mul],
      one_ne_zero⟩
  have hTT := Formalism.MainNotions.SchurRelationsDiscreteSeries.hypTT_all (D := D) u u'
  have hT : 0 < Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hT' : 0 < Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  have hW := fun j => Formalism.L2.SG.Pf.AmpWinRX.goodW_all Ch u u' (e (plE D j))
  have hA := fun j => goodS_of hB u u' (e (plE D j)) (Formalism.L2.SG.Pf.goodSRest_all hG hTies.dsig_tie hB u u' (e (plE D j)))
  have hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0 := fun j => (hc u _).ne'
  have hfpos : 0 < D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.BridgeLemma.szf_card_Tau]; exact hfpos)
  obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hcn
    push Not at hcn
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hfR 5
    norm_num at this; linarith
  have hrr : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by omega
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by omega) hn1801) ?_
    rw [hrr]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAch := le_of_le_of_eq (ac_le (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose) Cl L.sc.L D.R.rS D.R.k D.R.f hClp hf hL) (by rw [hrr])
  have h5 := Formalism.MainNotions.BridgeLemma.last_shifted_parameter_eq hH0.2.1
  have hDel : (D.s.Del : ℝ) ≠ 0 := by
    have := (Formalism.MainNotions.BridgeLemma.cfg_ok hH0.2.1 hS0 τ).hDel
    exact ne_of_gt (lt_of_lt_of_le one_pos this)
  set de := deOf D τ u with hde_def
  set de' := deOf D τ u' with hde'_def
  have hde := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel τ u
  have hde' := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel τ u'
  have hN := parNumsE_of (D := D) u u' e de de' h5 hde hde'
  have hty := typesE_of T.X Ch capacity_from_hermitian_char u u' e de de' h5 hde hde'
  set TP := tpOf T.X Ch Formalism.FourierDecayAlt.P.type_projectors_exist u u' e de de' i0' hN hty with hTPdef
  set Θ0 : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (T.X.Vloc u (tauE T.X e j)) (T.X.Vloc u' (tauE T.X e j)) :=
    fun _ => liftId with hΘ0
  set cc : Fin (nfE D) → ℂ := fun j => ccOneG Ch hB hJ L hCl hH0 u u' (e (plE D j)) hTT
    (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl (e (plE D j))) with hcc_def
  have hleaf := xLeafAt_of_pinsG T.X Ch hB hJ L hCl hH0 u u' e he (host_v D) 0 de de' 0 i0 i0' 1 ∅ ∅ νq 0 a b ξ ξ' hTT hW hA
    hT hT' hpin1 (fun j => hscl (e (plE D j))) hcO (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L)
    (fun j => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _) (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) _
    (le_max_left _ _) (le_max_right _ _) (fun _ => hAch) cc rfl
  have hpin := hleaf.2.2 Θ0 TP 0
  have hh0 : (0 : ℝ) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L / 2 := by
    have : (0 : ℝ) ≤ L.sc.L := by linarith
    positivity
  have hcc : CoefCC (ITc T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd i0' Θ0 TP 0) :=
    Formalism.L2.SG.Pf.CoefCCT.coefCC_carrierInTc Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) a b ξ ξ' cc cutStd
      (nuE T.X Ch u' e i0') (m0E T.X Ch u u' e) Θ0 TP 0 (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L)
      (fun _ => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _) (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) le_rfl
      (fun _ => hh0) (fun j => (ha j).1) (fun j => (hb j).1)
  have hcap := coefCap_ITc T.X Ch hS0 hCl hk18 u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) a b ξ ξ' cc cutStd
    i0' Θ0 TP 0 (fun j => (hb j).1)
  have hBuilt := isBuilt_carrierInT T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0)
    (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd (nuE T.X Ch u' e i0') (m0E T.X Ch u u' e) Θ0 TP 0 hN hty
    (frames_carrierInT T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd
      i0' Θ0 TP 0) hcc hcap
  have hJT := jointTensor_compact_test T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0)
    (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd i0 i0' hi Θ0 TP 0 1 νq hNu hpin one_pos hBuilt
  exact vIndepAt_of_tensorAt T.X u u' _ _ _ _ _ _ _ _ 1 i0 i0' νq hJT

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.TheoremSConclusion

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.PoincareAmplitudeLowerBounds

namespace GlobalTheory.CarrierGap
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.Pf.CarrierXAll.KFinDense] [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in
theorem theoremS_leaves_of_carrierG
    (hCar : CarrierP)
    (hNG : Formalism.L2.SG.RowsPos.RowNGP)
    (hRFD : Formalism.L2.SG.RowsDef.RowsFinDim) (wMU : CompanionTheory.Lime.BM.UniqGap)
    (bSW : _root_.PI.VolStabS.MassDataS.SWXS) :
    TheoremSClosedHypotheses := by
  have hFC : FormulaC := Formalism.L2.SG.Pf.Cnt.formulaCT_holds
  have kD := Formalism.L2.SG.Pf.CarrierXAll.kFinDense_holds
  have rVA : VIndepAtAllP :=
    vIndepAtAllP_ofG wMU (Formalism.L2.SG.Pf.CarrierXAll.kFinNZ_of kD)
  have rVP : Formalism.L2.SG.VolPin.VolumeOddGeneric := Formalism.L2.SG.Closed.volume_determined
  have hWu : Formalism.L2.SG.Pf.WuDecayOfGap := Formalism.L2.SG.Pf.wuDecayOfGap_of_uniqGap wMU
  have hDI := Formalism.L2.SG.Pf.Cnt.densInputT_holds
  have hLM : ∀ D : D7, Formalism.L2.SG.DataInst.LocalModelAt D := Formalism.L2.SG.Pf.localModelAt_holds
  exact ⟨hLM, hDI, fun D => rowsInputP_of_dataCut (Formalism.L2.SG.DataCut.rowsInputP_of_normProd (Formalism.L2.SG.Closed.NormProd_holds D)
    (Formalism.L2.SG.Pf.Coef.rowsDatumP_of_deep (Formalism.L2.SG.Closed.CutLeavesDeep_outright D))),
    hNG,
    Formalism.L2.SG.Closed.KppOffC_holds, hCar, kExpTiedS_holds,
    Formalism.L2.SG.Closed.FoldOKC_outright, Formalism.L2.SG.Closed.OOIntAllC_outright, Formalism.L2.SG.Closed.AbsConvC_outright,
    Formalism.L2.SG.Pf.finXC_of hWu hRFD, hWu, choicesC_holds,
    hFC, rowsSum_of_formula_volume hFC rVP, rowFormAllP_of hFC rVP rVA (Formalism.L2.SG.Pf.NcAllC.normalizing_constants_all Formalism.L2.SG.Closed.CovolRef_outright bSW), massDataInputsAll_of
      (massDataPosAll_of Formalism.L2.SG.Pf.ProdConvCut2.prodConvAll_holds bSW (fun X v => Formalism.L2.SG.Pf.MassDataX.dvPosC_holds X v) Formalism.L2.SG.Pf.MassDataX.densNonnegAll_holds)
      (Formalism.L2.SG.Pf.MassDataX.massDataVolAll_of bSW) Formalism.L2.SG.Pf.ProdConvCut2.prodConvAll_holds Formalism.L2.SG.Pf.MassDataX.typedAll_holds
      (fun _ hg X u u' => Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz wMU hg X u u' 1 one_pos) _root_.locFramePrim, linkAll_holds, splitAll_holds⟩

end GlobalTheory.CarrierGap
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn
namespace GlobalTheory.CarrierGap

theorem carrierP : Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨hPA, hMP, hBB⟩ := GlobalTheory.carrierNeedsFromD
  obtain ⟨Cb, hL⟩ := Formalism.L2.SG.Pf.CarrierXAll.liftAt3_exists
  exact Formalism.L2.SG.SpectralTiesReal.carrierP_of_compact_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb
    (Formalism.L2.SG.Pf.CarrierXAll.carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsPG CompanionTheory.Lime.BM.uniqGap_holds
      (xPinsP_ofG CompanionTheory.Lime.BM.uniqGap_holds
        (Formalism.L2.SG.Pf.CarrierXAll.kFinNZ_of Formalism.L2.SG.Pf.CarrierXAll.kFinDense_holds))))

theorem offDiag : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.RowsPos.RowNGP → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (𝒞 : FamClass) (sel : SSel 𝒞), (∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i)) → Formalism.L2.SG.Pf.SzHypFam.RanksRow 3 𝒞 → LoopRowS 3 𝒞 sel → Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm 3 (sel Fm hc) := by
  intro hSW hNG hRF 𝒞 sel hLoc hRk hLp
  have hWu : Formalism.L2.SG.Pf.WuDecayOfGap := CompanionTheory.Lime.BM.wuDecayOfGap_holds'
  have hTF := Formalism.L2.SG.Pf.SzHypFam.hTF_of_ranks 3 hRk
  have hOK := selOK_of 3 (Formalism.L2.SG.Pf.finXC_of hWu hRF) hWu sel hLoc hTF
  have hS : TheoremSDistinctWords := theoremS_distinct_of_closed (Formalism.L2.SG.TheoremSConclusion.theoremS_of_conj
    (theoremS_leaves_of_carrierG carrierP hNG hRF CompanionTheory.Lime.BM.uniqGap_holds hSW))
  exact offDiagonalK0_of_rows 3 hS (by norm_num) sel hOK
    (Formalism.L2.SG.Pf.SzHypOf.sizesRowS_of 3 sel (Formalism.L2.SG.Pf.SzHypFam.hRw_of_ranks 3 hRk)
      (Formalism.L2.SG.Pf.ThresholdLevels.thrRow_holds 3))
    (Formalism.L2.SG.Pf.SzHypFam.aSz 3) (Formalism.L2.SG.Pf.SzHypFam.hA_of_ranks 3 (by norm_num) hRk) hLp absConvTied_holds

end GlobalTheory.CarrierGap
end
