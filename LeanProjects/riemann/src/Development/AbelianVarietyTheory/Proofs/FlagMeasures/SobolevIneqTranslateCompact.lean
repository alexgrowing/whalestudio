import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInf.SobTranslate

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_mulLeft {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => a * g) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)).contDiff

theorem inUH_mul {n : ℕ} {H a g : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hg : inUH H g) :
    inUH H (a * g) := by
  unfold inUH at *
  rw [conjTranspose_mul]
  calc gᴴ * aᴴ * H * (a * g) = gᴴ * (aᴴ * H * a) * g := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha, hg]

theorem smoothOnH_translate {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H a : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) : SmoothOnH H (fun g => f (a * g)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (a * g₀) (inUH_mul ha hg₀)
  have hc := contDiff_mulLeft a
  refine ⟨(fun g => a * g) ⁻¹' U, fun g => F (a * g), hU.preimage hc.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hc.contDiffOn (fun _ h => h)
  · intro g hg hgH
    exact hfF _ hg (inUH_mul ha hgH)

end Smooth

theorem rdWord_translate {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : Matrix (Fin m) (Fin m) ℂ) (ws : List (Matrix (Fin m) (Fin m) ℂ))
    (f : Matrix (Fin m) (Fin m) ℂ → V) :
    rdWord ws (fun g => f (a * g)) = fun g => rdWord ws f (a * g) := by
  induction ws with
  | nil => rfl
  | cons X w ih =>
    funext g
    show rdM X (rdWord w _) g = rdM X (rdWord w f) (a * g)
    rw [ih]
    simp only [rdM, Matrix.mul_assoc]

variable {k r : ℕ}

theorem inv_of_mem {a : Mat k r} (ha : a ∈ GG k r) : a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 := by
  by_cases hdet : IsUnit a.det
  · exact ⟨Matrix.mul_nonsing_inv a hdet, Matrix.nonsing_inv_mul a hdet⟩
  · exfalso
    have h0 : a⁻¹ ∈ GG k r := (gg_closedSub k r).2.2.2.2 a ha
    rw [Matrix.nonsing_inv_apply_not_isUnit a hdet] at h0
    have h1 : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := h0
    let i : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
    have h2 : Hpk k r i i = -1 := by simp [Hpk, i]
    rw [← h1] at h2
    simp at h2

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurableEmbedding_lmul {a b : Mat k r} (hab : a * b = 1) (hba : b * a = 1) :
    MeasurableEmbedding (lmulM a : Mt k r → Mt k r) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := lmulM a
      invFun := lmulM b
      left_inv := fun x => by
        show b * (a * Matrix.of x) = x
        rw [← Matrix.mul_assoc, hba, Matrix.one_mul]
        rfl
      right_inv := fun x => by
        show a * (b * Matrix.of x) = x
        rw [← Matrix.mul_assoc, hab, Matrix.one_mul]
        rfl
      continuous_toFun := continuous_lmul a
      continuous_invFun := continuous_lmul b }
  exact e.measurableEmbedding

theorem lintegral_translate_le {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {a : Mat k r}
    (ha : a ∈ GG k r) {K₀ K₂ : Set (Mt k r)} (hK : ∀ y ∈ K₀, lmulM a y ∈ K₂)
    (φ : Mt k r → ENNReal) :
    ∫⁻ y in K₀, φ (lmulM a y) ∂μ ≤ ∫⁻ y in K₂, φ y ∂μ := by
  have hemb := measurableEmbedding_lmul (inv_of_mem ha).1 (inv_of_mem ha).2
  have hmap : μ.map (lmulM a) = μ := hμ.2.2.2 a ha
  calc ∫⁻ y in K₀, φ (lmulM a y) ∂μ ≤ ∫⁻ y in lmulM a ⁻¹' K₂, φ (lmulM a y) ∂μ :=
        lintegral_mono_set hK
    _ = ∫⁻ y, φ y ∂((μ.restrict (lmulM a ⁻¹' K₂)).map (lmulM a)) :=
        (hemb.lintegral_map _).symm
    _ = ∫⁻ y in K₂, φ y ∂μ := by
        rw [← hemb.restrict_map, hmap]

theorem ofReal_integral_le {α : Type*} [MeasurableSpace α] (ν : Measure α) (g : α → ℝ)
    (hg : ∀ y, 0 ≤ g y) : ENNReal.ofReal (∫ y, g y ∂ν) ≤ ∫⁻ y, ENNReal.ofReal (g y) ∂ν := by
  by_cases h : AEStronglyMeasurable g ν
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg) h]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable h]
    simp

theorem list_sum_ofReal {α : Type*} (l : List α) (u : α → ℝ) (v : α → ENNReal) (hu : ∀ a, 0 ≤ u a)
    (h : ∀ a ∈ l, ENNReal.ofReal (u a) ≤ v a) :
    0 ≤ (l.map u).sum ∧ ENNReal.ofReal (l.map u).sum ≤ (l.map v).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h0, h1⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨add_nonneg (hu a) h0, ?_⟩
    rw [ENNReal.ofReal_add (hu a) h0]
    exact add_le_add (h a List.mem_cons_self) h1

theorem sobolev_translate : ∀ (k r : ℕ) (μ : Measure (Mt k r)) (C₀ : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsHaarOn (GG k r) μ → IsCompact K₀ → (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C₀ * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μ).sum) → ∀ Q : Set (Mt k r), IsCompact Q → ∃ K₂ : Set (Mt k r), IsCompact K₂ ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → (∀ ws ∈ Ws, ContinuousOn (rdWord ws f) (GG k r)) → ∀ x ∈ Q, Matrix.of x ∈ GG k r → ENNReal.ofReal (‖f (Matrix.of x)‖ ^ 2) ≤ ENNReal.ofReal |C₀| * (Ws.map fun ws => ∫⁻ y in K₂, (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2 ∂μ).sum := by
  intro k r μ C₀ Ws K₀ hμ hK₀ hS Q hQ
  let pr : Mt k r × Mt k r → Mt k r := fun p => lmulM (Matrix.of p.1) p.2
  have hpr : Continuous pr := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [pr, lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  refine ⟨pr '' (Q ×ˢ K₀), (hQ.prod hK₀).image hpr, ?_⟩
  intro B _ _ _ f hf _ x hxQ hxG
  have hsm : SmoothOnH (Hpk k r) (fun g => f (Matrix.of x * g)) :=
    smoothOnH_translate (a := Matrix.of x) hxG hf
  have hkey := hS B (fun g => f (Matrix.of x * g)) hsm
  simp only [Matrix.mul_one, rdWord_translate] at hkey
  obtain ⟨hS0, hSum⟩ := list_sum_ofReal Ws
    (fun ws => ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ)
    (fun ws => ∫⁻ y in pr '' (Q ×ˢ K₀), (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2 ∂μ)
    (fun _ => integral_nonneg fun _ => by positivity)
    (fun ws _ => by
      refine (ofReal_integral_le _ _ fun _ => by positivity).trans ?_
      have hφ := lintegral_translate_le hμ (a := Matrix.of x) hxG (K₀ := K₀)
        (K₂ := pr '' (Q ×ˢ K₀)) (fun y hy => ⟨(x, y), ⟨hxQ, hy⟩, rfl⟩)
        (fun y => (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2)
      refine le_trans (le_of_eq ?_) hφ
      refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      rfl)
  calc ENNReal.ofReal (‖f (Matrix.of x)‖ ^ 2)
      ≤ ENNReal.ofReal (|C₀| * (Ws.map fun ws =>
          ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ).sum) :=
        ENNReal.ofReal_le_ofReal (hkey.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hS0))
    _ = ENNReal.ofReal |C₀| * ENNReal.ofReal (Ws.map fun ws =>
          ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ).sum :=
        ENNReal.ofReal_mul (abs_nonneg _)
    _ ≤ _ := by gcongr

end GlobalTheory.SgInf.SobTranslate
