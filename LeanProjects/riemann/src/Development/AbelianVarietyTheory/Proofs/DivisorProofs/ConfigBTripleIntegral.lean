import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationUnramifiedIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationArchimedeanIdentityStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeIntV

theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem integrableOn_tsum_translates {G ι : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] (s : Set G) (u : G → ℂ) (r : ι → G)
    (hu : AEStronglyMeasurable u μ)
    (hs : ∀ i, NullMeasurableSet ((fun g => (r i)⁻¹ * g) ⁻¹' s) μ)
    (hd : Pairwise (Function.onFun (AEDisjoint μ) fun i => (fun g => (r i)⁻¹ * g) ⁻¹' s))
    (hfin : ∫⁻ g in ⋃ i, (fun g => (r i)⁻¹ * g) ⁻¹' s, ‖u g‖ₑ ∂μ < ⊤) :
    IntegrableOn (fun g => ∑' i, u (r i * g)) s μ := by
  have hmp : ∀ i, MeasurePreserving (fun g => r i * g) μ μ := fun i => measurePreserving_mul_left μ (r i)
  have hm : ∀ i, AEStronglyMeasurable (fun g => u (r i * g)) (μ.restrict s) :=
    fun i => (hu.comp_measurePreserving (hmp i)).restrict
  refine ⟨(AEMeasurable.tsum fun i => (hm i).aemeasurable).aestronglyMeasurable, ?_⟩
  have key : ∀ i, ∫⁻ g in s, ‖u (r i * g)‖ₑ ∂μ = ∫⁻ g in (fun g => (r i)⁻¹ * g) ⁻¹' s, ‖u g‖ₑ ∂μ := by
    intro i
    have h1 := (hmp i).setLIntegral_comp_preimage_emb (MeasurableEquiv.mulLeft (r i)).measurableEmbedding
      (fun g => ‖u g‖ₑ) ((fun g => (r i)⁻¹ * g) ⁻¹' s)
    have h2 : (fun g => r i * g) ⁻¹' ((fun g => (r i)⁻¹ * g) ⁻¹' s) = s := by ext g; simp
    rw [h2] at h1
    exact h1
  show ∫⁻ g in s, ‖∑' i, u (r i * g)‖ₑ ∂μ < ⊤
  calc ∫⁻ g in s, ‖∑' i, u (r i * g)‖ₑ ∂μ ≤ ∫⁻ g in s, ∑' i, ‖u (r i * g)‖ₑ ∂μ :=
        lintegral_mono fun g => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ g in s, ‖u (r i * g)‖ₑ ∂μ := lintegral_tsum fun i => (hm i).aemeasurable.enorm
    _ = ∑' i, ∫⁻ g in (fun g => (r i)⁻¹ * g) ⁻¹' s, ‖u g‖ₑ ∂μ := tsum_congr key
    _ = ∫⁻ g in ⋃ i, (fun g => (r i)⁻¹ * g) ⁻¹' s, ‖u g‖ₑ ∂μ := (lintegral_iUnion₀ hs hd _).symm
    _ < ⊤ := hfin

theorem continuousMul_UA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : ContinuousMul (UA σ J) := by
  let e : UA σ J ≃* GAd σ ((1 : E) • J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (J := J) hσ one_ne_zero)
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  refine ⟨?_⟩
  have h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
    funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
  rw [h3]
  exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))

def stabRat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x₀ : Fin n → E) : Subgroup (UA σ J) where
  carrier := {q | q ∈ ratU σ J ∧ mat q *ᵥ incV F x₀ = incV F x₀}
  mul_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    refine ⟨(ratU σ J).mul_mem hp hq, ?_⟩
    show (mat p * mat q) *ᵥ incV F x₀ = incV F x₀
    rw [← Matrix.mulVec_mulVec, hq', hp']
  one_mem' := by
    refine ⟨(ratU σ J).one_mem, ?_⟩
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ incV F x₀ = incV F x₀
    exact Matrix.one_mulVec _
  inv_mem' := by
    rintro q ⟨hq, hq'⟩
    refine ⟨(ratU σ J).inv_mem hq, ?_⟩
    have h1 : mat q⁻¹ * mat q = 1 := by
      show ((q⁻¹ * q : UA σ J)).1.1 = 1
      rw [inv_mul_cancel]; rfl
    calc mat q⁻¹ *ᵥ incV F x₀ = mat q⁻¹ *ᵥ (mat q *ᵥ incV F x₀) := by rw [hq']
      _ = incV F x₀ := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem cone_integrable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ γ : {x : Fin a → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J, (∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H₀.x) → ∀ Φ ∈ PolData B G.M, ∀ h, IntegrableOn (fun g => ∑' x, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (γ x * g, h) Φ)))) G.M.dom G.M.μ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hEv γ hγ Φ hΦ h
  haveI := countable_numberField E
  have hG := hT.geo.hM
  haveI := hG.haar
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := continuousMul_UA (GlobalTheory.SiegelSet.sigma_sigma hT.base.cm) G.V.J
  haveI : MeasurableMul (UA σ G.V.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  have hA := GlobalTheory.T.second_configuration_triple_compatible hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hEv Φ hΦ h
  obtain ⟨hd, hfd⟩ := GlobalTheory.T.second_configuration_unramified_identity hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hEv γ hγ
  have hQ : ∀ q, q ∈ stabRat σ G.V.J H₀.x ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x := fun q => Iff.rfl
  have hB2 := GlobalTheory.T.second_configuration_archimedean_identity hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hEv Φ hΦ h
    (stabRat σ G.V.J H₀.x) hQ _ (hfd _ hQ)
  exact integrableOn_tsum_translates G.M.μ G.M.dom
    (fun g => thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ)))) γ hA
    (fun x => hG.dom.nullMeasurableSet.preimage (measurePreserving_mul_left G.M.μ _).quasiMeasurePreserving) hd hB2

end GlobalTheory.ConeIntV

end
