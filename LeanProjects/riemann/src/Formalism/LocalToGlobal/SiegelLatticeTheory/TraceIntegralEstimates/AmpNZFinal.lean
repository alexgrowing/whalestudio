import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpNZTie
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomTie
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefDecay

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

def AmpOrbCoefDD : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl → ∀ (D : D7) (large₂ : SizeData₂ D),
    Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
      (A : LocS W) (hA : GoodS D (lamD D τ) A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (v v' : A.H) (l : W.Wp) (l' : W.Wq) (ξ : W.Wp) (ξ' : W.Wq) (κ : ℂ), κ ≠ 0 ∧
      v ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ ∧
      v' ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ ∧
      Formalism.FourierDecayAlt.ThreeDimData.be W.z (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').c W.π A.σ W.μW
                (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').μN v v = (innerSL ℂ l).smulRight l ∧
      Formalism.FourierDecayAlt.ThreeDimData.be W.z' (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').c W.π' A.σ W.μW'
                (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').μN v' v' = (innerSL ℂ l').smulRight l' ∧
      ⟪l, ξ⟫_ℂ ≠ 0 ∧ ⟪ξ', l'⟫_ℂ ≠ 0 ∧
      OrbEq D hW hA hT hT' (fun g => κ • Formalism.MainNotions.S.Pv.AmpDD.coefF (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT')
        v v' ξ ξ' g)

theorem ampNZCoef_of (hE : AmpOrbCoefDD) (hCI : Formalism.MainNotions.S.Pv.BetaCut.CoefInCC)
    (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) : AmpNZCoef := by
  intro Cg cb Cu cT CT C0
  obtain ⟨A1, B1, hE'⟩ := hE Cg cb Cu cT CT C0
  refine ⟨A1, max B1 1000, fun C' Cl hC' hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec => ?_⟩
  have hCl1 : B1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl2 : (1000 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨v, v', l, l', ξ, ξ', κ, hκ, hv, hv', hbe, hbe', hl, hl', hOrb⟩ :=
    hE' C' Cl hC' hCl1 D large₂ hH τ w w' hTT θ W hW A hA hT hT'
  refine ⟨_, hOrb, ?_⟩
  set L := toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT' with hLdef
  have hk2 : 2 ≤ D.R.k := by have := Formalism.MainNotions.BridgeLemma.five_le_k D; omega

  have hv0 : 0 < D.host.v := by
    unfold Host.v Host.rdE
    refine div_pos (Real.rpow_pos_of_pos (abs_pos.2 ?_) _) two_pos
    exact_mod_cast NumberField.discr_ne_zero D.host.E
  have hka0 : 0 < D.host.ka := by unfold Host.ka; exact div_pos Real.pi_pos hv0
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  set ka : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) with hka
  have hkapos : 0 < ka := by positivity
  have hc : L.c = ((2 * ka : ℝ) : ℂ) := by
    show (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) = _
    congr 1; rw [hka]; ring

  have hW' := hW
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hNq, hq, -⟩ := hW'
  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := by
    intro h0
    have hμN : W.μN = 0 := by rw [hNq, h0]; unfold haarLie; rw [zero_smul]
    have hS0 : muS W.μW W.μN = 0 := by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]
    have h1 := hq (fun _ => 1) measurable_const
    rw [hS0] at h1
    simp at h1
    exact hG.2.1 h1

  have hL1 : (1 : ℝ) ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) (le_of_lt large₂.sc.eps_pos)
  obtain ⟨-, hTie⟩ := Formalism.L2.S.Pv.Mom.paramTieG_of hH.1 0 (by rw [abs_zero, add_zero]; nlinarith)
  have hl0 : l1dist (lamD D τ) (lamD D τ) ≤ 0 * D.R.k * (D.R.m : ℝ) ^ 3 := by
    unfold l1dist; simp
  obtain ⟨h, hgap, hok⟩ := hTie τ (lamD D τ) hl0 (Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc τ))
  have hsm : jNorm2 L (fun g => κ • Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ' g) μsec =
      ENNReal.ofReal (‖κ‖ ^ 2) * jNorm2 L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') μsec :=
    Formalism.MainNotions.BesselShellMomentBounds.jNorm2_smul L κ _ μsec
  rw [hsm]
  refine mul_ne_zero (ENNReal.ofReal_pos.2 (pow_pos (norm_pos_iff.2 hκ) 2)).ne' ?_
  exact Formalism.L2.S.Pv.AmpNZTie.jNorm2_coef_ne' hk2 L ka hkapos hc hκ0 hκtop μsec hsec h hgap hok v v' hv hv'
    l l' ξ ξ' hbe hbe' hl hl' hCI hBI

theorem coefficients_in_compact_closure : Formalism.MainNotions.S.Pv.BetaCut.CoefInCC := by
  intro k r ε lam H _ _ _ σ h m A hlam hσ hgap hm hA v hv v' hv' Wp Wq _ _ _ _ ξ ξ'
  exact Formalism.L2.SG.Pf.CoefDecay.coefM_inCC hlam hgap m hm hA hσ hv hv' ξ ξ' 5

theorem ampNZ_of_parts (hE : AmpOrbCoefDD) (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) : AmpNZ :=
  ampNZ_of (ampNZCoef_of hE coefficients_in_compact_closure hBI)

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem amplitude_uniform_of_coefficients (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt) (hE : AmpOrbCoefDD)
    (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) : AmpUnif :=
  Formalism.L2.S.Pv.AmpFinal.amplitude_uniform_of_orbit hJ hKD hRJ hRH hOQ hRA (ampNZ_of_parts hE hBI)

end Formalism.MainNotions.S.Pv.LemmaJ
