import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionBoundedOnUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipIntSo

open GlobalTheory.ThKContSmall

theorem cont_inv (hP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (hT : IsTriple B G X om om') (Φ' : _) (hSo : Φ' ∈ G.M'.So B.ψ B.τ₁) :
    Continuous (G.M'.I om' Φ') ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  have hPair := isPair_small hT
  have hS : Φ' ∈ schA F _ := so_le_schA hT.geo.hM' _ hSo
  have hB := (GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ' hS
  refine ⟨?_, fun γ hγ h => ?_⟩
  · obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ' hSo 0
    haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
    have hv := measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
    have hht : Continuous (fun h : UA σ G.W.J => (ht h : ℝ)) :=
      NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : SecondCountableTopology (AE F E) := by
      obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
      exact e.secondCountableTopology
    haveI hMat : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) :=
      inferInstanceAs (SecondCountableTopology (Fin (a + a') → Fin (a + a') → AE F E))
    haveI : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))ᵐᵒᵖ :=
      (MulOpposite.opHomeomorph (M := Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))).symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin (a + a')) (AE F E)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    haveI : SecondCountableTopology (UA σ G.W.J) :=
      (Topology.IsEmbedding.subtypeVal (p := fun x : GL (Fin (a + a')) (AE F E) =>
        x ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J))).secondCountableTopology
    haveI : FirstCountableTopology (UA σ G.W.J) :=
      TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    rw [continuous_iff_continuousAt]
    intro h₀
    have hev : ∀ᶠ h in 𝓝 h₀, (ht h : ℝ) < ht h₀ + 1 :=
      hht.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    unfold Model.I
    refine continuousAt_of_dominated (bound := fun _ => max C 0 * ((ht h₀ : ℝ) + 1) ^ k) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun h =>
        (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hev] with h hh
      refine Eventually.of_forall fun g => ?_
      have h1 := hC g h
      rw [pow_zero, mul_one] at h1
      calc ‖theta om' Φ' g h‖ ≤ C * (ht h : ℝ) ^ k := h1
        _ ≤ max C 0 * (ht h : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ max C 0 * ((ht h₀ : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh.le _) (le_max_right _ _)
    · exact integrableOn_const hv.ne
    · exact Eventually.of_forall fun g =>
        (hB.1.comp (continuous_const.prodMk continuous_id)).continuousAt
  · unfold Model.I
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have e := hB.2.1 1 (one_mem _) γ hγ g h
    rw [one_mul] at e
    exact e

theorem integrableOn_unip : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, IntegrableOn (fun u : unip σ G.W H' => G.M'.I om' Φ (u.1 * h)) 𝓕 μ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' Φ hΦ μ 𝓕 hμ h𝓕 h1 h
  obtain ⟨hc, hinv⟩ := cont_inv hKP F E σ B a a' G X om om' hT Φ hΦ
  obtain ⟨C, hC⟩ := GlobalTheory.ThK.UnipBound.bounded_on_unip F E σ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hT.base hT.geo.hW hH' _
    hc hinv h
  obtain ⟨i1, -, -, -⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hcont : Continuous (fun u : unip σ G.W H' => G.M'.I om' Φ (u.1 * h)) :=
    hc.comp (continuous_subtype_val.mul continuous_const)
  have hfin : μ 𝓕 ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  refine Measure.integrableOn_of_bounded hfin hcont.aestronglyMeasurable (M := C) ?_
  exact Filter.Eventually.of_forall fun u => hC u.1 u.2

end GlobalTheory.ThK.UnipIntSo

end
