import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.ExpansionAverage

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem integrable_K {E : Type} [NormedAddCommGroup E] {F : KG ε → E} (hF : Continuous F) : Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem toMK_mem (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integrable_Dw (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Integrable (fun k : KG ε => e k • Dw σ l (σ (toMK k) w)) (muK ε) :=
  integrable_K (he.smul ((h.continuousOn_Dw hl hw).comp_continuous (continuous_toMK ε) toMK_mem))

theorem Dw_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    Dw σ l (kAvg ε σ e w) = ∫ k, e k • Dw σ l (σ (toMK k) w) ∂(muK ε) := by
  refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
  have h0 : Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) := integrable_Dw h he (l := []) (by simp) hw
  rw [inner_Dw h.1 hl hy hw', kAvg, ← integral_inner h0, ← integral_inner (integrable_Dw h he hl hw),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_Dw h.1 hl hy (hw.translate h.1 (toMK_mem k))]
  ring

theorem form_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ)
    {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    ℓ (kAvg ε σ e w) = ∫ k, e k * ℓ (σ (toMK k) w) ∂(muK ε) := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  have hΛ' : ∀ w, Sm ε σ w → ℓ w = ∑ i, Λ i (Dw σ (S i) w) := hΛ
  rw [hΛ' _ hw']
  simp only [fun i => Dw_kAvg h he (hS i) hw hw',
    fun i => ((Λ i).integral_comp_comm (integrable_Dw h he (hS i) hw)).symm]
  rw [← integral_finsetSum _ fun i _ => (Λ i).integrable_comp (integrable_Dw h he (hS i) hw)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [hΛ' _ (hw.translate h.1 (toMK_mem k)), Finset.mul_sum, map_smul, smul_eq_mul]

theorem continuousOn_and_hasSum_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (S : List (List (Mx n))) (v : ℕ → H) (ℓ : ℕ → (H →ₗ[ℂ] ℂ)) (C : ℕ → ℝ) (f : Mx n → ℂ),
      Words (lieSet ε) S → Ctrl (lieSet ε) (UJset ε) σ S → IsExpn (lieSet ε) (UJset ε) σ S v ℓ C f →
      ContinuousOn f (UJset ε) ∧ ∀ e : KG ε → ℂ, Continuous e → (∀ w, Sm ε σ (kAvg ε σ e w)) → ∀ g ∈ UJset ε,
        HasSum (fun i => ℓ i (σ g (kAvg ε σ e (v i)))) (∫ k, e k * f (g * toMK k) ∂(muK ε)) := by
  intro n ε H _ _ _ σ h S v ℓ C f hS ⟨B, hB, hBd⟩ hE
  have hsc := hE.sobCont hS
  obtain ⟨hv, hC, hb, hsum, hf⟩ := hE
  have hc : ∀ i, ContinuousOn (fun g => ℓ i (σ g (v i))) (UJset ε) := fun i => h.continuousOn_coef (hsc i) (hv i)
  have hbd : ∀ (M : ℝ) i, ∀ g ∈ UJset ε, B g ≤ M → ‖ℓ i (σ g (v i))‖ ≤ M * (C i * sobNorm σ S (v i)) := by
    intro M i g hg hM
    calc ‖ℓ i (σ g (v i))‖ ≤ C i * sobNorm σ S (σ g (v i)) := hb i _ (Sm.translate h.1 (hv i) hg)
      _ ≤ C i * (M * sobNorm σ S (v i)) := mul_le_mul_of_nonneg_left
          ((hBd g hg _ (hv i)).trans (mul_le_mul_of_nonneg_right hM (sobNorm_nonneg _ _ _))) (hC i)
      _ = _ := by ring
  refine ⟨fun g₀ hg₀ => ?_, fun e he hs g hg => ?_⟩
  · have ho : {g | B g < B g₀ + 1} ∈ 𝓝 g₀ := (isOpen_lt hB continuous_const).mem_nhds (lt_add_one (B g₀))
    have h1 : ContinuousOn (fun g => ∑' i, ℓ i (σ g (v i))) (UJset ε ∩ {g | B g < B g₀ + 1}) :=
      continuousOn_tsum (fun i => (hc i).mono Set.inter_subset_left) (hsum.mul_left (B g₀ + 1))
        fun i g hg => hbd _ i g hg.1 (le_of_lt hg.2)
    have h2 : ContinuousOn f (UJset ε ∩ {g | B g < B g₀ + 1}) := h1.congr fun g hg => (hf g hg.1).tsum_eq.symm
    exact (continuousWithinAt_inter ho).1 (h2 g₀ ⟨hg₀, lt_add_one (B g₀)⟩)
  · have hm : ∀ k : KG ε, g * toMK k ∈ UJset ε := fun k => mul_mem_UJ hg (toMK_mem k)
    have hcm : Continuous fun k : KG ε => g * toMK k := continuous_const.mul (continuous_toMK ε)
    obtain ⟨M, hM⟩ := (isCompact_range (hB.comp hcm)).bddAbove
    have hM' : ∀ k : KG ε, B (g * toMK k) ≤ M := fun k => hM ⟨k, rfl⟩
    have hF : ∀ i, Integrable (fun k : KG ε => e k * ℓ i (σ (g * toMK k) (v i))) (muK ε) := fun i =>
      integrable_K (he.mul ((hc i).comp_continuous hcm hm))
    have hS' : Summable fun i => ∫ k, ‖e k * ℓ i (σ (g * toMK k) (v i))‖ ∂(muK ε) := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) (fun i => ?_)
        ((hsum.mul_left M).mul_left (∫ k, ‖e k‖ ∂(muK ε)))
      rw [← integral_mul_const]
      refine integral_mono (hF i).norm ((integrable_K he.norm).mul_const _) fun k => ?_
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd M i _ (hm k) (hM' k)) (norm_nonneg _)
    have key := hasSum_integral_of_summable_integral_norm hF hS'
    simp only [fun k => ((hf _ (hm k)).mul_left (e k)).tsum_eq] at key
    refine Eq.mpr (congrArg (HasSum · _) (funext fun i => ?_)) key
    have := form_kAvg h he (sobCont_translate h.1 (hsc i) hg) (hv i) (hs (v i))
    simp only [fun k => sigma_mul h.1 hg (toMK_mem k)]
    exact this

end GlobalTheory.ExpansionAverage

end
