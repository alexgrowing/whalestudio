import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingIntegralCountableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLeviClosureMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentMeasureFormulaStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.UnfoldQ

theorem mat_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem isLevi_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H : Plane E d d₁) {t t' : (AE F E)ˣ} {h₁ h₁' : UA σ W₁.J}
    {h h' : UA σ W.J} (e : IsLevi H t h₁ h) (e' : IsLevi H t' h₁' h') : IsLevi H (t * t') (h₁ * h₁') (h * h') := by
  obtain ⟨ex, ey, eι⟩ := e
  obtain ⟨ex', ey', eι'⟩ := e'
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul', ← Matrix.mulVec_mulVec, ex', Matrix.mulVec_smul, ex, smul_smul, Units.val_mul, mul_comm]
  · rw [mat_mul', ← Matrix.mulVec_mulVec, ey', Matrix.mulVec_smul, ey, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [mat_mul', mat_mul', Matrix.mul_assoc, eι', ← Matrix.mul_assoc, eι, Matrix.mul_assoc]

theorem ideles_lcsc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem unfold_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ (μN : Measure (unip σ G.V H)) (c : ENNReal), μN.IsHaarMeasure → c ≠ 0 → c ≠ ⊤ → (∀ φ : UA σ G.V.J → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂G.M.μ = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, φ (n.1 * m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂μN ∂G₁.M.μ ∂μ ∂μK) →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ φ : UA σ G.V.J → ENNReal, Continuous φ →
      (∀ q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}, ∀ g, φ (q * g) = φ g) →
      (∀ n ∈ unip σ G.V H, ∀ g, φ (n * g) = φ g) →
      ∫⁻ g in 𝓓, φ g ∂G.M.μ = C * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, φ (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ K μK μ hK hμK hμ m hm μN c hμN hc0 hctop hI
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) G.V.J
  obtain ⟨hTG₁, hLC₁, hSC₁, hT2₁⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ b G₁.V.J
  obtain ⟨hTGi, hLCi, hSCi⟩ := ideles_lcsc F E
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.V.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := hG.hM.haar
  haveI := hG₁.hM.haar
  haveI : SigmaCompactSpace (UA σ G₁.V.J) := inferInstance
  haveI : SigmaCompactSpace (AE F E)ˣ := inferInstance
  haveI : SFinite G₁.M.μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts G₁.M.μ)
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  haveI : Countable (ratU σ G.V.J) := GlobalTheory.QDom.countable_ratU σ G.V.J
  haveI : Countable (ratU σ G₁.V.J) := GlobalTheory.QDom.countable_ratU σ G₁.V.J
  obtain ⟨𝓕, h𝓕, h𝓕0, h𝓕top⟩ := GlobalTheory.T.unipotent_fundamental_domain_exists F E σ B b a' G G₁ H H' hC hB hG hG₁ μN hμN
  have hNQ : unip σ G.V H ≤ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x} :=
    Subgroup.closure_mono fun u hu => hu.1
  have hsub : (ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}).subgroupOf (unip σ G.V H) = (ratU σ G.V.J).subgroupOf (unip σ G.V H) := by
    ext n
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hNQ n.2⟩⟩
  refine ⟨c * μN 𝓕, mul_ne_zero hc0 h𝓕0, ENNReal.mul_ne_top hctop h𝓕top, ?_⟩
  intro 𝓓 h𝓓 φ hφ hφQ hφN
  have hmul : ∀ l g₀, ∀ γ ∈ ratU σ G₁.V.J, m l (γ * g₀) = m 1 γ * m l g₀ := by
    intro l g₀ γ _
    refine GlobalTheory.T.levi_lift_unique F E σ B b a' G G₁ H H' hC hB hG hG₁ l (γ * g₀) _ _ (hm l (γ * g₀)) ?_
    simpa only [one_mul] using isLevi_mul H (hm 1 γ) (hm l g₀)
  have hιQ : ∀ γ ∈ ratU σ G₁.V.J, m 1 γ ∈ (ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) := by
    intro γ hγ
    obtain ⟨h, hr, hl⟩ := GlobalTheory.T.rational_unitary_levi_lift F E σ B b a' G G₁ H H' hC hB hG hG₁ γ hγ
    rw [← GlobalTheory.T.levi_lift_unique F E σ B b a' G G₁ H H' hC hB hG hG₁ 1 γ h (m 1 γ) hl (hm 1 γ)]
    refine ⟨hr, Subgroup.subset_closure ?_⟩
    show mat h *ᵥ incV F H.x = incV F H.x
    rw [hl.1, Units.val_one, one_smul]
  have hcont := GlobalTheory.T.levi_map_continuous F E σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  have hjoint : Measurable (fun p : unip σ G.V H × UA σ G₁.V.J × (AE F E)ˣ × K => p.1.1 * m p.2.2.1 p.2.1 * p.2.2.2.1) := by
    apply Continuous.measurable
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (hcont.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd)))).mul
      (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  have habs : ∀ l : (AE F E)ˣ, 0 < (absE F E l : ℝ) := by
    intro l
    have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))
  have hw : Measurable fun l : (AE F E)ˣ => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).measurable.pow_const _)
  have hw0 : ∀ l : (AE F E)ˣ, ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ≠ 0 := fun l =>
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (habs l) _)).ne'
  have hQc : Countable ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) := (Subgroup.inclusion_injective (inf_le_left : (ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) ≤ ratU σ G.V.J)).countable
  exact GlobalTheory.T.unfolding_integral_countable G.M.μ G₁.M.μ μ μK (unip σ G.V H) (ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) (ratU σ G₁.V.J) μN (fun k : K => k.1) m (fun γ => m 1 γ)
    (fun l => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)))) c G₁.M.dom 𝓕
    hQc inferInstance inferInstance inferInstance (fun g => (continuous_mul_left g).measurable)
    (fun g => (continuous_mul_left g).measurable) (fun g => (continuous_mul_right g).measurable) hjoint hw hw0 (fun _ => ENNReal.ofReal_ne_top) inferInstance hI hc0 hctop
    hmul hιQ (GlobalTheory.T.rational_levi_closure_mem F E σ B b a' G G₁ H H' hC hB hG hG₁ m hm)
    (GlobalTheory.T.levi_unipotent_measure_formula F E σ B b a' G G₁ H H' hC hB hG hG₁ m hm μN hμN) inferInstance (hsub ▸ h𝓕) h𝓕0 h𝓕top hG₁.hM.dom inferInstance
    𝓓 h𝓓 φ (hφ.measurable) hφQ hφN

end GlobalTheory.UnfoldQ
