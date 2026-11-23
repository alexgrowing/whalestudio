import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopologyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory.RightRegFund

theorem isRightReg_props (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hR : I.IsRightReg μf fund R) :
    R 1 = 1 ∧ (∀ g h, R (g * h) = R g * R h) ∧ (∀ g F, ‖R g F‖ = ‖F‖) ∧
      (∀ F, Continuous fun g => R g F) ∧ ∀ F : I.L2 μf fund,
        (∀ᵐ y ∂(I.muA μf), ∀ γ ∈ I.GFset, I.ext F (γ * y) = I.ext F y) ∧
          AEStronglyMeasurable (I.ext F) (I.muA μf) := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : IsFiniteMeasureOnCompacts (I.muA μf) := by
    unfold AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  refine ⟨map_one hD hfund.1 hr hR, map_mul hD hfund.1 hr hR, norm_map hD hfund.1 hr hR,
    continuous_map hD hfund.1 hr hR, fun F => ⟨?_, ?_⟩⟩
  · refine (ae_good hD).mono fun y hy γ hγ => ?_
    have hm : γ ∈ (Γ : Set I.GA) := hΓ ▸ hγ
    unfold AutInst.ext
    rw [rep_mul hr hy ⟨γ, hm⟩]
  · exact aestronglyMeasurable_comp_rep hD hfund.1 hr (Lp.stronglyMeasurable F)

theorem rightReg_unitary_continuous : ∀ B : RowsAut, B.R 1 = 1 ∧ (∀ g h, B.R (g * h) = B.R g * B.R h) ∧ (∀ g F, ‖B.R g F‖ = ‖F‖) ∧ (∀ F, Continuous fun g => B.R g F) ∧ ∀ F : B.I.L2 B.μf B.fund, (∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, B.I.ext F (γ * y) = B.I.ext F y) ∧ AEStronglyMeasurable (B.I.ext F) (B.I.muA B.μf) :=
  fun B => isRightReg_props B.I B.μf B.fund B.fund_spec B.R B.R_spec

end GlobalTheory.RightRegFund
