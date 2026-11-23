import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKInvBig

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem I_weil_left : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), ∀ (g : UA σ G.V.J) (h : UA σ G.W.J), G.M.I om (om (g, 1) Ψ) h = G.M.I om Ψ h := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT Ψ hΨ g' h
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hKP.base
  have hP := GlobalTheory.ThKContSmall.isPair_big hT
  have hB := (hTB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP).1 Ψ hΨ
  have hM := hT.geo.hM
  haveI := hM.haar
  obtain ⟨htg, hlc, hsc, ht2⟩ := GlobalTheory.UnipCT.topFacts σ G.V.J
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.V.J
  haveI : MeasurableMul (UA σ G.V.J) := inferInstance
  haveI : SigmaCompactSpace (UA σ G.V.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite G.M.μ := Measure.IsHaarMeasure.sigmaFinite G.M.μ
  haveI : SFinite G.M.μ := inferInstance
  haveI : MeasurableConstSMul (ratU σ G.V.J) (UA σ G.V.J) :=
    ⟨fun γ => (measurable_const_mul (γ.1 : UA σ G.V.J))⟩
  haveI : SMulInvariantMeasure (ratU σ G.V.J) (UA σ G.V.J) G.M.μ := ⟨fun γ A _ => measure_preimage_mul G.M.μ γ.1 A⟩
  have hfin : G.M.μ G.M.dom < ⊤ :=
    GlobalTheory.ThKContSmall.measure_dom_lt_top hKP.siegelSetUnitary hT.base hT.geo.hV hM
  have hR : G.M.μ.map (· * g') = G.M.μ := by
    haveI : (G.M.μ.map (· * g')).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right G.M.μ g'
    have hc := Measure.isMulLeftInvariant_eq_smul (G.M.μ.map (· * g')) G.M.μ
    set c := Measure.haarScalarFactor (G.M.μ.map (· * g')) G.M.μ
    have h𝓕' : IsFundamentalDomain (ratU σ G.V.J) ((· * g') ⁻¹' G.M.dom) G.M.μ := by
      refine hM.dom.preimage_of_equiv (quasiMeasurePreserving_mul_right G.M.μ g') (e := id) Function.bijective_id ?_
      intro γ x
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
    have hm : G.M.μ ((· * g') ⁻¹' G.M.dom) = G.M.μ G.M.dom := h𝓕'.measure_eq hM.dom
    have h0 : G.M.μ G.M.dom ≠ 0 := hM.dom.measure_ne_zero (NeZero.ne G.M.μ)
    have hmap : (G.M.μ.map (· * g')) G.M.dom = G.M.μ ((· * g') ⁻¹' G.M.dom) :=
      MeasurableEquiv.map_apply (MeasurableEquiv.mulRight g') G.M.dom
    have h1 : (c : ENNReal) * G.M.μ G.M.dom = 1 * G.M.μ G.M.dom := by
      calc (c : ENNReal) * G.M.μ G.M.dom = (c • G.M.μ) G.M.dom := by simp [Measure.smul_apply]
        _ = (G.M.μ.map (· * g')) G.M.dom := by rw [← hc]
        _ = 1 * G.M.μ G.M.dom := by rw [one_mul]; exact hmap.trans hm
    have hc1 : c = 1 := by
      have := (ENNReal.mul_left_inj h0 hfin.ne).1 h1
      exact_mod_cast this
    rw [hc, hc1, one_smul]
  have hmp : MeasurePreserving (· * g') G.M.μ G.M.μ := ⟨measurable_mul_const g', hR⟩
  have hemb : MeasurableEmbedding (· * g' : UA σ G.V.J → UA σ G.V.J) :=
    (MeasurableEquiv.mulRight g').measurableEmbedding
  have h𝓕' : IsFundamentalDomain (ratU σ G.V.J) ((· * g') ⁻¹' G.M.dom) G.M.μ := by
    refine hM.dom.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  set f : UA σ G.V.J → ℂ := fun x => theta om Ψ x h with hf
  have hk : ∀ x, theta om (om (g', 1) Ψ) x h = f (x * g') := by
    intro x
    simp only [hf, theta]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hinv : ∀ (γ : ratU σ G.V.J) (x : UA σ G.V.J), f (γ • x * g') = f (x * g') := by
    intro γ x
    simp only [hf, Subgroup.smul_def, smul_eq_mul, mul_assoc]
    have e := hB.2.1 γ.1 γ.2 1 (one_mem _) (x * g') h
    rwa [one_mul] at e
  unfold Model.I
  simp_rw [hk]
  calc ∫ x in G.M.dom, f (x * g') ∂G.M.μ = ∫ x in (· * g') ⁻¹' G.M.dom, f (x * g') ∂G.M.μ :=
        hM.dom.setIntegral_eq h𝓕' hinv
    _ = ∫ y in G.M.dom, f y ∂G.M.μ := hmp.setIntegral_preimage_emb hemb f G.M.dom

end GlobalTheory.ThKInvBig

end
