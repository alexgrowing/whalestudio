import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.PeriodLift

theorem exists_matrix_lift {r : ℕ} {ι : Type} {𝓕 : Filter ι} (p : Fin r → Prop) [DecidablePred p]
    (A₀ : Matrix (Fin r) (Fin r) ℂ) (A : ι → Matrix (Fin r) (Fin r) ℂ)
    (h0 : A₀.det ≠ 0) (hA : ∀ᶠ n in 𝓕, (A n).det ≠ 0)
    (hc : ∀ a, p a → ∀ k, Tendsto (fun n => A n k a) 𝓕 (𝓝 (A₀ k a)))
    (hr : ∀ a, ¬ p a → ∀ k, Tendsto (fun n => (A n)⁻¹ a k) 𝓕 (𝓝 (A₀⁻¹ a k))) :
    ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 A₀) ∧ ∀ᶠ n in 𝓕,
      (∀ a, p a → ∀ k, B n k a = A n k a) ∧ (∀ a, ¬ p a → ∀ k, (B n)⁻¹ a k = (A n)⁻¹ a k) := by
  set Q : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun k a => if p a then A n k a else A₀ k a with hQdef
  set D : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun a j =>
      if p a then (1 : Matrix (Fin r) (Fin r) ℂ) a j else ((A n)⁻¹ * Q n) a j with hDdef
  have hQe : ∀ k a, Tendsto (fun n => Q n k a) 𝓕 (𝓝 (A₀ k a)) := by
    intro k a
    by_cases h : p a
    · simpa [hQdef, h] using hc a h k
    · simpa [hQdef, h] using tendsto_const_nhds
  have hQ : Tendsto Q 𝓕 (𝓝 A₀) :=
    tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => hQe k a
  have hD : Tendsto D 𝓕 (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun j => ?_
    by_cases h : p a
    · simpa [hDdef, h] using tendsto_const_nhds
    · have e : (1 : Matrix (Fin r) (Fin r) ℂ) a j = ∑ k, A₀⁻¹ a k * A₀ k j := by
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (Ne.isUnit h0)]
      rw [e]
      simp only [hDdef, Matrix.of_apply, h, if_false, Matrix.mul_apply]
      exact tendsto_finset_sum _ fun k _ => (hr a h k).mul (hQe k j)
  have hdet : Continuous fun M : Matrix (Fin r) (Fin r) ℂ => M.det := continuous_id.matrix_det
  have hDi : Tendsto (fun n => (D n)⁻¹) 𝓕 (𝓝 1) := by
    have hc1 : ContinuousAt Inv.inv (1 : Matrix (Fin r) (Fin r) ℂ) := by
      apply continuousAt_matrix_inv
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have := hc1.tendsto.comp hD
    simpa [Function.comp_def] using this
  have hQd : ∀ᶠ n in 𝓕, (Q n).det ≠ 0 := ((hdet.tendsto _).comp hQ).eventually_ne h0
  have hDd : ∀ᶠ n in 𝓕, (D n).det ≠ 0 :=
    ((hdet.tendsto _).comp hD).eventually_ne (by simp)
  refine ⟨fun n => Q n * (D n)⁻¹, by simpa using hQ.mul hDi, ?_⟩
  filter_upwards [hA, hQd, hDd] with n hAn hQn hDn
  constructor
  · intro j hj k
    have hDj : ∀ i, D n i j = (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
      intro i
      by_cases h : p i
      · simp [hDdef, h]
      · rw [← Matrix.nonsing_inv_mul _ (Ne.isUnit hAn)]
        simp [hDdef, hQdef, h, hj, Matrix.mul_apply]
    have e : (Q n * (D n)⁻¹ * D n) k j = (Q n * (D n)⁻¹ * (1 : Matrix (Fin r) (Fin r) ℂ)) k j := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [hDj]
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_right _ _ (Ne.isUnit hDn)] at e
    rw [← e]
    simp [hQdef, hj]
  · intro a ha k
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit hDn)]
    have e : ((A n)⁻¹ * Q n * (Q n)⁻¹) a k = (A n)⁻¹ a k := by
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit hQn)]
    rw [← e, Matrix.mul_apply, Matrix.mul_apply]
    simp [hDdef, ha]

theorem tendsto_of_span {E : Type} [Field E] {r : ℕ} {ι : Type} {𝓕 : Filter ι}
    (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ : ι → (Fin r → E) → ℂ) (Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ n v w, Φ n (v + w) = Φ n v + Φ n w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ n (c : E) v, Φ n (c • v) = σ c * Φ n v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0)
    (h : ∀ v ∈ S, Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v))) (v : Fin r → E) :
    Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v)) := by
  have hv : v ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e : (0 : Fin r → E) = (0 : E) • (0 : Fin r → E) := by simp
    rw [e]
    simp only [hs, hs₀, hσ, zero_mul]
    exact tendsto_const_nhds
  | add x y _ _ hx hy => simpa only [ha, ha₀] using hx.add hy
  | smul c x _ hx => simpa only [hs, hs₀] using hx.const_mul (σ c)

theorem hermC_emb_inv_col {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (u : Fin r → ℂ) (k : Fin r) :
    hermC τ G u (Data.emb τ fun b => cc (G⁻¹ b k)) = u k := by
  have e : ∀ a, ∑ b, u a * τ (G a b) * (starRingEnd ℂ) (τ (cc (G⁻¹ b k))) =
      u a * τ ((G * G⁻¹) a k) := by
    intro a
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.conj_conj, map_mul, mul_assoc]
  simp only [hermC, Data.emb, e]
  rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hG)]
  simp [Matrix.one_apply, apply_ite τ]

theorem period_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ι : Type) (𝓕 : Filter ι) (x₀ : Frame X.Ψ r) (x₁ : ι → Frame X.Ψ r), x₀ ∈ X.dom → (∀ᶠ n in 𝓕, x₁ n ∈ X.dom) → (∀ v ∈ X.Λ, ∀ (τ : X.Ψ) (a : Fin r), Tendsto (fun n => (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)) 𝓕 (𝓝 (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v) else ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a))) → ∀ V ∈ 𝓝 x₀, ∀ᶠ n in 𝓕, ∃ x ∈ V, ∀ (v : Fin r → E) (τ : X.Ψ) (a : Fin r), (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v) else ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a) = (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a) := by
  intro E _ _ _ r X ι 𝓕 x₀ x₁ h0 h1 h V hV
  have key : ∀ τ : X.Ψ, ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 (mat x₀ τ)) ∧
      ∀ᶠ n in 𝓕, (∀ a : Fin r, (a : ℕ) < X.p0 → ∀ k, B n k a = mat (x₁ n) τ k a) ∧
        (∀ a : Fin r, ¬ (a : ℕ) < X.p0 → ∀ k, (B n)⁻¹ a k = (mat (x₁ n) τ)⁻¹ a k) := by
    intro τ
    refine exists_matrix_lift (fun a : Fin r => (a : ℕ) < X.p0) (mat x₀ τ)
      (fun n => mat (x₁ n) τ) (h0 τ).1 (h1.mono fun n hn => (hn τ).1) ?_ ?_
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => (starRingEnd ℂ) (τ.1 c))
        (fun n v => hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v))
        (fun v => hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v))
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_true] using h v hv τ a)
        (fun b => cc (X.Gm⁻¹ b k))
      simpa only [hermC_emb_inv_col τ.1 X.Gm X.Gm_det, col] using this
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun n v => ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun v => ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_false] using h v hv τ a)
        (Pi.single k 1)
      simpa [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply, apply_ite τ.1] using this
  choose B hB hB' using key
  have hx : Tendsto (fun n => (fun τ => B τ n : Frame X.Ψ r)) 𝓕 (𝓝 x₀) :=
    tendsto_pi_nhds.2 fun τ => hB τ
  filter_upwards [hx.eventually_mem hV, eventually_all.2 hB'] with n hn hn'
  refine ⟨_, hn, fun v τ a => ?_⟩
  have hm : mat (fun τ => B τ n : Frame X.Ψ r) τ = B τ n := rfl
  rw [hm]
  by_cases ha : (a : ℕ) < X.p0
  · have : col (B τ n) a = col (mat (x₁ n) τ) a := funext fun k => (hn' τ).1 a ha k
    simp only [ha, if_true, this]
  · simp only [ha, if_false, Matrix.mulVec, dotProduct, (hn' τ).2 a ha]

end GlobalTheory.PeriodLift
