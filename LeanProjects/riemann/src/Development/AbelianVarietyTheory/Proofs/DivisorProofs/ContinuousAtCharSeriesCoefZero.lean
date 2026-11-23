import Mathlib

open Filter Topology

namespace GlobalTheory.CharSeriesCoef

noncomputable def avg {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y)
    (χ : AddChar Y ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, χ (w i)

theorem norm_avg_le_one_of {ι : Type} [Fintype ι] (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, f i‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast h
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hc, mul_one]
  calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum (fun i _ => hf i)
    _ = Fintype.card ι := by simp

theorem avg_prod {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y) (y : Y) (K : ℕ)
    (χ : AddChar Y ℂ) :
    avg (fun ik : ι × Fin K => w ik.1 + (ik.2 : ℕ) • y) χ
      = avg w χ * ((K : ℂ)⁻¹ * ∑ k : Fin K, χ y ^ (k : ℕ)) := by
  unfold avg
  rw [Fintype.sum_prod_type]
  simp only [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [← Finset.sum_mul_sum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [mul_inv]
  ring

theorem geom_avg_le {ζ : ℂ} (hζ : ζ ≠ 1) (h1 : ‖ζ‖ = 1) (K : ℕ) (hK : 0 < K) :
    ‖(K:ℂ)⁻¹ * ∑ k : Fin K, ζ ^ (k:ℕ)‖ ≤ 2 / (K * ‖ζ - 1‖) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) K, geom_sum_eq hζ K]
  have hz : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hnum : ‖ζ ^ K - 1‖ ≤ 2 := by
    calc ‖ζ ^ K - 1‖ ≤ ‖ζ ^ K‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, h1]; norm_num
  rw [norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (K:ℝ)⁻¹ * (‖ζ ^ K - 1‖ / ‖ζ - 1‖) ≤ (K:ℝ)⁻¹ * (2 / ‖ζ - 1‖) := by gcongr
    _ = 2 / (K * ‖ζ - 1‖) := by field_simp

theorem exists_avg {Y Ξ : Type} [AddCommGroup Y] [Zero Ξ] (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (δ : ℝ) (hδ : 0 < δ) (T : Finset Ξ) (h0 : (0:Ξ) ∉ T) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (w : ι → Y),
      ∀ b ∈ T, ‖avg w (e b)‖ ≤ δ := by
  classical
  revert h0
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨Unit, inferInstance, inferInstance, fun _ => 0, by simp⟩
  · intro a T ha ih h0
    have ha0 : a ≠ 0 := fun h => h0 (by simp [h])
    have hT0 : (0:Ξ) ∉ T := fun h => h0 (Finset.mem_insert_of_mem h)
    obtain ⟨ι, _, _, w, hw⟩ := ih hT0
    obtain ⟨y, hy⟩ := hne a ha0
    have hz : 0 < ‖e a y - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / (δ * ‖e a y - 1‖))
    have hK0 : (0:ℝ) < K := lt_trans (by positivity) hK
    have hKn : 0 < K := by exact_mod_cast hK0
    haveI : Nonempty (Fin K) := ⟨⟨0, hKn⟩⟩
    refine ⟨ι × Fin K, inferInstance, inferInstance,
      fun ik => w ik.1 + (ik.2 : ℕ) • y, ?_⟩
    intro b hb
    rw [avg_prod, norm_mul]
    have hA : ‖avg w (e b)‖ ≤ 1 := norm_avg_le_one_of _ (fun i => (hn b _).le)
    have hG : ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 := by
      have := norm_avg_le_one_of (ι := Fin K) (fun k => e b y ^ (k:ℕ))
        (fun k => by rw [norm_pow, hn]; simp)
      simpa using this
    rcases Finset.mem_insert.mp hb with rfl | hbT
    · have hg := geom_avg_le hy (hn b y) K hKn
      have : 2 / (K * ‖e b y - 1‖) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hK
        nlinarith
      calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 * δ := by
            gcongr
            exact hg.trans this
        _ = δ := one_mul δ
    · calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ δ * 1 := by
            gcongr
            exact hw b hbT
        _ = δ := mul_one δ

theorem continuousAt_coef_zero {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P]
    (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (he0 : ∀ y, e 0 y = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ) (hM : Summable M)
    (hb : ∀ᶠ p in 𝓝 p0, ∀ a, ‖c p a‖ ≤ M a)
    (hc : ∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) :
    ContinuousAt (fun p => c p 0) p0 := by
  classical
  have hM0 : ∀ a, 0 ≤ M a := fun a => (norm_nonneg _).trans (hb.self_of_nhds a)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set S := ∑' a, M a with hSdef
  have hS : 0 ≤ S := tsum_nonneg hM0
  obtain ⟨s, hs⟩ : ∃ s : Finset Ξ, S - ∑ a ∈ s, M a < ε / 6 := by
    have h2 := (Metric.tendsto_nhds.mp hM.hasSum) (ε / 6) (by positivity)
    obtain ⟨s, hs⟩ := h2.exists
    refine ⟨s, ?_⟩
    rw [Real.dist_eq] at hs
    linarith [neg_abs_le (∑ a ∈ s, M a - S)]
  set δ := ε / 6 / (S + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδS : δ * S ≤ ε / 6 := by
    have : δ * (S + 1) = ε / 6 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨ι, _, _, w, hw⟩ := exists_avg e hn hne δ hδ (s.erase 0) (by simp)
  set α : Ξ → ℂ := fun b => avg w (e b) with hαdef
  have hα1 : ∀ b, ‖α b‖ ≤ 1 := fun b => norm_avg_le_one_of _ (fun i => (hn b _).le)
  have hα0 : α 0 = 1 := by
    simp only [hαdef, avg, he0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  let A : P → ℂ := fun p => (Fintype.card ι : ℂ)⁻¹ * ∑ i, ∑' a, e a (w i) * c p a
  have hAc : ContinuousAt A p0 :=
    continuousAt_const.mul (tendsto_finset_sum _ (fun i _ => hc (w i)))

  have key : ∀ p, (∀ a, ‖c p a‖ ≤ M a) → ‖A p - c p 0‖ ≤ δ * S + (S - ∑ a ∈ s, M a) := by
    intro p hp
    have hsum : ∀ i, HasSum (fun a => e a (w i) * c p a) (∑' a, e a (w i) * c p a) := by
      intro i
      refine (Summable.of_norm_bounded hM (fun a => ?_)).hasSum
      rw [norm_mul, hn, one_mul]; exact hp a
    have h1 : HasSum (fun a => α a * c p a) (A p) := by
      have := (hasSum_sum (s := Finset.univ) (fun i _ => hsum i)).mul_left
        ((Fintype.card ι : ℂ)⁻¹)
      have hfun : (fun a => α a * c p a)
          = fun a => (Fintype.card ι : ℂ)⁻¹ * ∑ i, e a (w i) * c p a := by
        funext a
        simp only [hαdef, avg, Finset.sum_mul, mul_assoc]
      rw [hfun]; exact this
    have h2 : HasSum (fun a : Ξ => if a = (0:Ξ) then c p 0 else 0) (c p 0) := hasSum_ite_eq (0:Ξ) (c p 0)
    have h3 : HasSum (fun a => α a * c p a - if a = 0 then c p 0 else 0) (A p - c p 0) :=
      HasSum.sub h1 h2
    have hg : HasSum (fun a => δ * M a + (M a - if a ∈ s then M a else 0))
        (δ * S + (S - ∑ a ∈ s, M a)) := by
      refine (hM.hasSum.mul_left δ).add (hM.hasSum.sub ?_)
      have : HasSum (fun a => if a ∈ s then M a else 0) (∑ b ∈ s, if b ∈ s then M b else 0) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => if_neg hb)
      have e2 : (∑ b ∈ s, if b ∈ s then M b else 0) = ∑ b ∈ s, M b :=
        Finset.sum_congr rfl (fun b hb => if_pos hb)
      rw [e2] at this
      exact this
    refine h3.norm_le_of_bounded hg (fun a => ?_)
    have hMa := hM0 a
    by_cases ha : a = 0
    · subst ha
      simp only [hα0, one_mul, if_true, sub_self, norm_zero]
      split_ifs <;> nlinarith [mul_nonneg hδ.le hMa]
    · simp only [ha, if_false, sub_zero]
      by_cases has : a ∈ s
      · simp only [has, if_true, sub_self, add_zero]
        rw [norm_mul]
        have := hw a (Finset.mem_erase.mpr ⟨ha, has⟩)
        exact mul_le_mul this (hp a) (norm_nonneg _) hδ.le
      · simp only [has, if_false, sub_zero]
        rw [norm_mul]
        have : ‖α a‖ * ‖c p a‖ ≤ 1 * M a := mul_le_mul (hα1 a) (hp a) (norm_nonneg _) zero_le_one
        nlinarith
  have hAev := (Metric.tendsto_nhds.mp hAc) (ε / 3) (by positivity)
  have hp0 := key p0 hb.self_of_nhds
  filter_upwards [hb, hAev] with p hp hAp
  have hpk := key p hp
  rw [dist_eq_norm] at hAp ⊢
  have : c p 0 - c p0 0 = -(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0) := by ring
  rw [this]
  calc ‖-(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0)‖
      ≤ ‖-(A p - c p 0)‖ + ‖A p - A p0‖ + ‖A p0 - c p0 0‖ := norm_add₃_le
    _ < ε := by rw [norm_neg]; linarith

end GlobalTheory.CharSeriesCoef

theorem GlobalTheory.continuousAt_charSeries_coef_zero :
    ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 :=
  fun e hn he0 hne c p0 M hM hb hc =>
    GlobalTheory.CharSeriesCoef.continuousAt_coef_zero e hn he0 hne c p0 M hM hb hc
