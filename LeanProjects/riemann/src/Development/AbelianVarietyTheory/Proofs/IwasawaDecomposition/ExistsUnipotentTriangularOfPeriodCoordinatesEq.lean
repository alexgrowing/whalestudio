import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendsto
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt hermC cc)
open scoped Matrix

namespace GlobalTheory.PeriodUnipotent

theorem eq_of_span {E : Type} [Field E] {r : ℕ} (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ v w, Φ (v + w) = Φ v + Φ w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ (c : E) v, Φ (c • v) = σ c * Φ v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0) (h : ∀ v ∈ S, Φ v = Φ₀ v) (v : Fin r → E) : Φ v = Φ₀ v :=
  tendsto_const_nhds_iff.1 (GlobalTheory.PeriodLift.tendsto_of_span (𝓕 := (⊤ : Filter Unit)) S hS σ (fun _ => Φ) Φ₀
    (fun _ => ha) ha₀ (fun _ => hs) hs₀ hσ (fun v hv => by rw [h v hv]; exact tendsto_const_nhds) v)

theorem inv_mul_apply {r p : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hc : ∀ a : Fin r, (a : ℕ) < p → ∀ k, B k a = A k a)
    (hr : ∀ a : Fin r, ¬ (a : ℕ) < p → ∀ k, B⁻¹ a k = A⁻¹ a k) (a c : Fin r) (hac : c ≤ a) :
    (A⁻¹ * B) a c = (1 : Matrix (Fin r) (Fin r) ℂ) a c := by
  by_cases h : (c : ℕ) < p
  · rw [← Matrix.nonsing_inv_mul A (Ne.isUnit hA)]
    simp only [Matrix.mul_apply, hc c h]
  · have h' : ¬ (a : ℕ) < p := by
      have : (c : ℕ) ≤ a := hac
      omega
    rw [← Matrix.nonsing_inv_mul B (Ne.isUnit hB)]
    simp only [Matrix.mul_apply, hr a h']

theorem exists_unipotent_of_pc_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x x' : Frame X.Ψ r), x ∈ X.dom → x' ∈ X.dom → (∀ v ∈ X.Λ, ∀ τ a, GlobalTheory.GenericFrames.pc X x' v τ a = GlobalTheory.GenericFrames.pc X x v τ a) → ∃ b ∈ Bor X.Ψ r, (∀ τ i, b τ i i = 1) ∧ x' = rmul x b := by
  intro E _ _ _ r X x x' hx hx' h
  have key : ∀ (τ : X.Ψ) (a c : Fin r), c ≤ a →
      ((mat x τ)⁻¹ * mat x' τ) a c = (1 : Matrix (Fin r) (Fin r) ℂ) a c := by
    intro τ
    refine inv_mul_apply (p := X.p0) _ _ (hx τ).1 (hx' τ).1 ?_ ?_
    · intro a ha k
      have := eq_of_span (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => (starRingEnd ℂ) (τ.1 c))
        (fun v => hermC τ.1 X.Gm (col (mat x' τ) a) (Data.emb τ.1 v))
        (fun v => hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v))
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [GlobalTheory.GenericFrames.pc, ha, if_true] using h v hv τ a)
        (fun b => cc (X.Gm⁻¹ b k))
      simpa only [GlobalTheory.PeriodLift.hermC_emb_inv_col τ.1 X.Gm X.Gm_det, col] using this
    · intro a ha k
      have := eq_of_span (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun v => ((mat x' τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun v => ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [GlobalTheory.GenericFrames.pc, ha, if_false] using h v hv τ a)
        (Pi.single k 1)
      simpa [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply, apply_ite τ.1] using this
  refine ⟨fun τ => ((mat x τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
    fun τ i => ?_, funext fun τ => ?_⟩
  · change ((mat x τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit (hx τ).1)).ne_zero (hx' τ).1
  · exact (key τ a c hca.le).trans (Matrix.one_apply_ne hca.ne')
  · exact (key τ i i le_rfl).trans (Matrix.one_apply_eq i)
  · change mat x' τ = mat x τ * ((mat x τ)⁻¹ * mat x' τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit (hx τ).1)]

end GlobalTheory.PeriodUnipotent
