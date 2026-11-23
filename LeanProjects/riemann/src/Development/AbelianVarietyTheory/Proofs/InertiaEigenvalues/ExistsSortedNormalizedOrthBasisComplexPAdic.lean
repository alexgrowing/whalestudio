import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PMonE.OrthBasis

private lemma exists_orthogonal_translate (l : ℕ) [Fact l.Prime] (W : Submodule ℚ_[l] ℂ_[l])
    [FiniteDimensional ℚ_[l] W] (x : ℂ_[l]) (hx : x ∉ W) :
    ∃ y : ℂ_[l], y - x ∈ W ∧ y ≠ 0 ∧ ∀ w ∈ W, ‖y‖ ≤ ‖y + w‖ ∧ ‖w‖ ≤ ‖y + w‖ := by
  haveI : ProperSpace W := FiniteDimensional.proper ℚ_[l] W
  obtain ⟨w₀, hw₀K, hmin⟩ := (isCompact_closedBall (0 : W) ‖x‖).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
    (Continuous.continuousOn (f := fun w : W => ‖x - (w : ℂ_[l])‖) (by fun_prop))
  have h0 : ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x‖ := by
    simpa using hmin (Metric.mem_closedBall_self (norm_nonneg x) : (0 : W) ∈ _)
  have hglob : ∀ w : W, ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x - (w : ℂ_[l])‖ := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : W) ‖x‖
    · exact hmin hw
    · have hlt : ‖x‖ < ‖(w : ℂ_[l])‖ := by simpa using hw
      have h1 : ‖x - (w : ℂ_[l])‖ = ‖(w : ℂ_[l])‖ := by
        rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hlt.ne),
          norm_neg, max_eq_right hlt.le]
      rw [h1]; exact h0.trans hlt.le
  refine ⟨x - w₀, by simpa using W.neg_mem w₀.2, ?_, fun w hw => ⟨?_, ?_⟩⟩
  · intro h
    exact hx (by rw [sub_eq_zero.1 h]; exact w₀.2)
  · have := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    simpa [sub_sub_eq_add_sub, sub_add_eq_add_sub, add_sub_assoc] using this
  · have h1 := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    have h2 : w = (x - w₀ + w) + -(x - w₀) := by abel
    calc ‖w‖ = ‖(x - w₀ + w) + -(x - w₀)‖ := by rw [← h2]
      _ ≤ max ‖x - w₀ + w‖ ‖-(x - w₀)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖x - w₀ + w‖ := by
        rw [norm_neg]
        refine max_le le_rfl ?_
        have : x - (↑(⟨w₀ - w, W.sub_mem w₀.2 hw⟩ : W) : ℂ_[l]) = x - w₀ + w := by simp; abel
        rw [← this]; exact h1

private lemma exists_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] :
    ∀ (n : ℕ) (μ : Fin n → ℂ_[l]), LinearIndependent ℚ_[l] μ →
      ∃ u : Fin n → ℂ_[l], (∀ i, u i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧ (∀ i, u i ≠ 0) ∧
        ∀ (c : Fin n → ℚ_[l]) (j : Fin n),
          ‖c j‖ * ‖u j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * u i‖ := by
  intro n
  induction n with
  | zero => intro μ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ j => j.elim0⟩
  | succ n ih =>
    intro μ hμ
    rw [← Fin.snoc_init_self μ, linearIndependent_fin_snoc] at hμ
    obtain ⟨hμ₀, hx⟩ := hμ
    obtain ⟨u₀, hu₀S, hu₀, horth⟩ := ih _ hμ₀
    set W := Submodule.span ℚ_[l] (Set.range (Fin.init μ))
    haveI : FiniteDimensional ℚ_[l] W :=
      FiniteDimensional.span_of_finite ℚ_[l] (Set.finite_range _)
    obtain ⟨y, hyx, hy0, hy⟩ := exists_orthogonal_translate l W _ hx
    have hWS : W ≤ Submodule.span ℚ_[l] (Set.range μ) := by
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩
    have hxS : μ (Fin.last n) ∈ Submodule.span ℚ_[l] (Set.range μ) :=
      Submodule.subset_span ⟨_, rfl⟩
    refine ⟨Fin.snoc (α := fun _ => ℂ_[l]) u₀ y, fun i => ?_, fun i => ?_, fun c j => ?_⟩
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simp only [Fin.snoc_last]
        have : y = μ (Fin.last n) + (y - μ (Fin.last n)) := by abel
        rw [this]; exact Submodule.add_mem _ hxS (hWS hyx)
      · simp only [Fin.snoc_castSucc]; exact hWS (hu₀S k)
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa using hy0
      · simpa using hu₀ k
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      set w := ∑ i : Fin n, algebraMap ℚ_[l] ℂ_[l] (c i.castSucc) * u₀ i
      have hw : w ∈ W := Submodule.sum_mem _ fun i _ => by
        rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hu₀S i)
      have key : ‖c (Fin.last n)‖ * ‖y‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ ∧
          ‖w‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ := by
        by_cases hc : c (Fin.last n) = 0
        · simp [hc]
        · set a := algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))
          have hna : ‖a‖ = ‖c (Fin.last n)‖ := norm_algebraMap' ℂ_[l] _
          have ha : a ≠ 0 := by
            intro h; apply hc; rw [← norm_eq_zero, ← hna, h, norm_zero]
          have hw' : a⁻¹ * w ∈ W := by
            rw [show a⁻¹ = algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))⁻¹ by simp [a],
              ← Algebra.smul_def]
            exact Submodule.smul_mem _ _ hw
          obtain ⟨h1, h2⟩ := hy _ hw'
          have e : w + a * y = a * (y + a⁻¹ * w) := by field_simp; ring
          rw [e, norm_mul, hna]
          refine ⟨mul_le_mul_of_nonneg_left h1 (norm_nonneg _), ?_⟩
          have : ‖w‖ = ‖c (Fin.last n)‖ * ‖a⁻¹ * w‖ := by
            rw [norm_mul, norm_inv, hna, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc),
              one_mul]
          rw [this]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa using key.1
      · simp only [Fin.snoc_castSucc]
        exact (horth (fun i => c i.castSucc) k).trans key.2

private lemma exists_rescale_norm_mem_Ioc (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (hx : x ≠ 0) :
    ∃ t : ℚ_[l], t ≠ 0 ∧ (l : ℝ)⁻¹ < ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ∧
      ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ≤ 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := zero_lt_one.trans hl
  obtain ⟨n, h1, h2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.2 hx) hl
  have hN : ‖algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ (n + 1)) * x‖ = ‖x‖ / (l : ℝ) ^ (n + 1) := by
    rw [norm_mul, norm_algebraMap', norm_zpow, Padic.norm_p, inv_zpow, div_eq_inv_mul]
  refine ⟨(l : ℚ_[l]) ^ (n + 1), zpow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero),
    ?_, ?_⟩
  · rw [hN, lt_div_iff₀ (zpow_pos hlpos _), zpow_add_one₀ hlpos.ne', mul_comm _ (l : ℝ), ← mul_assoc,
      inv_mul_cancel₀ hlpos.ne', one_mul]
    exact h1
  · rw [hN, div_le_one (zpow_pos hlpos _)]
    exact h2

private lemma exists_sorted_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l])
    (hμ : LinearIndependent ℚ_[l] μ) :
    ∃ v : Fin h → ℂ_[l], (∀ i, v i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧
      (∀ i, v i ≠ 0 ∧ ‖v i‖ ≤ 1) ∧ (∀ i, (l : ℝ)⁻¹ < ‖v i‖) ∧ Antitone (fun i => ‖v i‖) ∧
      ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
        ‖c j‖ * ‖v j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * v i‖ := by
  obtain ⟨u, huS, hu0, horth⟩ := exists_orthogonal_family_in_span l h μ hμ
  choose t ht0 htlo hthi using fun i => exists_rescale_norm_mem_Ioc l (u i) (hu0 i)
  set w : Fin h → ℂ_[l] := fun i => algebraMap ℚ_[l] ℂ_[l] (t i) * u i with hw_def
  have hworth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
      ‖c j‖ * ‖w j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * w i‖ := by
    intro c j
    have := horth (fun i => c i * t i) j
    simp only [hw_def, map_mul, mul_assoc, norm_mul, norm_algebraMap'] at this ⊢
    exact this
  set σ := Tuple.sort (fun i => -‖w i‖)
  refine ⟨fun i => w (σ i), fun i => ?_, fun i => ⟨?_, hthi _⟩, fun i => htlo _, ?_, fun c j => ?_⟩
  · simp only [hw_def]
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (huS _)
  · simp only [hw_def]
    intro h0
    have := congrArg norm h0
    rw [norm_zero] at this
    exact (lt_irrefl (0 : ℝ)) ((inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)).trans
      (this ▸ htlo (σ i)))
  · intro a b hab
    exact neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖w i‖) hab)
  · have := hworth (fun k => c (σ.symm k)) (σ j)
    rw [← Equiv.sum_comp σ] at this
    simpa using this

theorem _root_.GlobalTheory.PMonE.OrthBasis.exists_orthBasis : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), (∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0) → ∃ (P : Matrix (Fin h) (Fin h) ℚ_[l]) (μ' : Fin h → ℂ_[l]), P.det ≠ 0 ∧ (∀ i, μ' i = ∑ j, algebraMap ℚ_[l] ℂ_[l] (P i j) * μ j) ∧ (∀ i, μ' i ≠ 0 ∧ ‖μ' i‖ ≤ 1) ∧ Antitone (fun i => ‖μ' i‖) ∧ (∀ i j, ‖μ' i‖ < l * ‖μ' j‖) ∧ ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ' j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ' i‖ := by
  intro l _ h μ hind
  classical
  have hμ : LinearIndependent ℚ_[l] μ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := hind g (by simpa [Algebra.smul_def] using hg)
    simp [this]
  obtain ⟨v, hvS, hv1, hvlo, hanti, horth⟩ := exists_sorted_orthogonal_family_in_span l h μ hμ
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (hvS i)
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨Matrix.of P, v, ?_, fun i => ?_, hv1, hanti, fun i j => ?_, horth⟩
  · intro hdet
    obtain ⟨w, hw0, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    have hcol : ∀ j, ∑ i, w i * P i j = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct] using congrFun hwP j
    have hsum : ∑ i, algebraMap ℚ_[l] ℂ_[l] (w i) * v i = 0 := by
      simp_rw [← Algebra.smul_def, ← hP, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hcol, zero_smul, Finset.sum_const_zero]
    apply hw0
    funext j
    have h1 := horth w j
    rw [hsum, norm_zero] at h1
    have h2 : 0 < ‖v j‖ := norm_pos_iff.2 (hv1 j).1
    have h3 : ‖w j‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w j)]) (norm_nonneg _)
    simpa using h3
  · rw [← hP i]
    simp [Algebra.smul_def]
  · calc ‖v i‖ ≤ 1 := (hv1 i).2
      _ = (l : ℝ) * (l : ℝ)⁻¹ := (mul_inv_cancel₀ hlpos.ne').symm
      _ < (l : ℝ) * ‖v j‖ := mul_lt_mul_of_pos_left (hvlo j) hlpos

end GlobalTheory.PMonE.OrthBasis
