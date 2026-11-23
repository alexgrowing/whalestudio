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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipRightInv

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem integral_mul_right : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), ∀ n ∈ unip σ G.W H', ∫ u in 𝓕, G.M.I om Ψ (u.1 * n) ∂μ = ∫ u in 𝓕, G.M.I om Ψ u.1 ∂μ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH μ 𝓕 hμ h𝓕 h1 Ψ hΨ n hn
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ G.W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have h2 := hH.xy
    rw [h0] at h2
    simp [form] at h2
  have hcl := GlobalTheory.UnipClosed.isClosed_unip F E σ _ _ G.W H' hx0
  haveI : LocallyCompactSpace (unip σ G.W H') := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ G.W H') :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := GlobalTheory.UnipMass.countable_ratU' σ G.W.J (unip σ G.W H')
  haveI := hμ
  haveI h_a : SigmaCompactSpace (unip σ G.W H') := inferInstance
  haveI h_b : BorelSpace (unip σ G.W H') := inferInstance
  haveI h_c : IsLocallyFiniteMeasure μ := inferInstance
  haveI h_d : SigmaFinite μ := inferInstance
  haveI h_e : RegularSpace (unip σ G.W H') := inferInstance
  haveI h_f : TopologicalSpace.PseudoMetrizableSpace (unip σ G.W H') := inferInstance
  haveI h_g : μ.InnerRegular := inferInstance

  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hK.base
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  let f : unip σ G.W H' → ℂ := fun u => G.M.I om Ψ u.1
  have hinv : ∀ (γ : (ratU σ G.W.J).subgroupOf (unip σ G.W H')) (x : unip σ G.W H'), f (γ • x) = f x := by
    intro γ x
    have hγ : ((γ.1 : unip σ G.W H') : UA σ G.W.J) ∈ ratU σ G.W.J := Subgroup.mem_subgroupOf.1 γ.2
    have hth := ((hTB F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hV).1 Ψ hΨ).2.1
    show G.M.I om Ψ (((γ.1 : unip σ G.W H') : UA σ G.W.J) * x.1) = G.M.I om Ψ x.1
    unfold Model.I
    congr 1
    funext g
    simpa using hth 1 (one_mem _) _ hγ g x.1

  let nn : unip σ G.W H' := ⟨n, hn⟩
  let e : unip σ G.W H' ≃ᵐ unip σ G.W H' := MeasurableEquiv.mulRight nn
  set T : Set (unip σ G.W H') := (fun x => x * nn⁻¹) ⁻¹' 𝓕 with hT_def
  have hTfd : IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) T μ :=
    h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ nn⁻¹) Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  have hpre : e ⁻¹' T = 𝓕 := by
    ext x
    simp [e, T]

  have hmap : Measure.map e μ = μ := by
    have h0 : Measure.map e μ = Measure.modularCharacterFun nn • μ :=
      Measure.map_right_mul_eq_modularCharacterFun_smul μ nn
    have hA : Measure.map e μ T = 1 := by rw [e.map_apply, hpre, h1]
    have hB : μ T = 1 := by rw [hTfd.measure_eq h𝓕, h1]
    have hc : Measure.modularCharacterFun nn = 1 := by
      rw [h0, Measure.smul_apply, hB, ENNReal.smul_def, smul_eq_mul, mul_one] at hA
      exact_mod_cast hA
    rw [h0, hc, one_smul]
  have key := setIntegral_map_equiv (μ := μ) e f T
  rw [hmap, hpre] at key
  show ∫ u in 𝓕, f (e u) ∂μ = ∫ u in 𝓕, f u ∂μ
  rw [← key]
  exact hTfd.setIntegral_eq h𝓕 hinv

end GlobalTheory.UnipRightInv
