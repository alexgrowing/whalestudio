import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds
import Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm

namespace Formalism.GM

namespace ProgressionMeanBounds

open Finset Polynomial

lemma geom (p : ℝ) (hp : 2 ≤ p) (h : ℕ) :
    ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i = (1 - 1 / p ^ h) / (p - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    field_simp
    ring

lemma sumS (p : ℝ) (hp : 2 ≤ p) (Y₀ h : ℕ) :
    ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) ≤ (Y₀ : ℝ) / (p - 1) + h := by
  have hp1 : 0 < p - 1 := by linarith
  have e : ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) = (Y₀ : ℝ) * ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i + h := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    · simp
  rw [e, geom p hp h]
  have hY : (0 : ℝ) ≤ Y₀ := Nat.cast_nonneg _
  have hq : 0 ≤ 1 / p ^ h := by positivity
  have : (Y₀ : ℝ) * ((1 - 1 / p ^ h) / (p - 1)) ≤ (Y₀ : ℝ) / (p - 1) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hp1]
    nlinarith
  linarith

lemma swap {K ι : Type} (W : Finset ι) (roots : Multiset K) (f : ι → K → ℝ) :
    ∑ t ∈ W, (roots.map (f t)).sum = (roots.map (fun ζ => ∑ t ∈ W, f t ζ)).sum := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Finset.sum_add_distrib, ih]

theorem binK_natDegree_le (K : Type) [Field K] (k : ℕ) : (binK K k).natDegree ≤ k := by
  unfold binK
  exact (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree K k).le

theorem binMatK_entry_natDegree_le (K : Type) [Field K] {n : ℕ} (del₀ : ℕ)
    (c : Fin n → Fin n → ℕ → K) (i j : Fin n) : ((binMatK K del₀ c) i j).natDegree ≤ del₀ := by
  unfold binMatK
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ del₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (natDegree_C_mul_le _ _).trans ((binK_natDegree_le K k).trans hk')

theorem binMatK_det_natDegree_le (K : Type) [Field K] {n : ℕ} (del₀ : ℕ)
    (c : Fin n → Fin n → ℕ → K) : ((binMatK K del₀ c).det).natDegree ≤ del₀ * n := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  rw [Units.smul_def]
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, ((binMatK K del₀ c) (σ i) i).natDegree ≤ ∑ _i : Fin n, del₀ :=
        Finset.sum_le_sum (fun i _ => binMatK_entry_natDegree_le K del₀ c (σ i) i)
    _ = del₀ * n := by simp [mul_comm]

end ProgressionMeanBounds

open Finset Polynomial ProgressionMeanBounds

theorem windowMeanAP_of (hC : WindowCountAP) (hD : DiscsDisjointAP) : WindowMeanAP := by
  intro p _ K _ _ _ roots lam La₀ E n₀ del₀ t₀ d Y₀ h β hd hY hYp hE hcard hlam hj
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hY0 : (0 : ℝ) < Y₀ := by exact_mod_cast hY
  have hsum : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤
      ∑ j ∈ range Y₀, ((lam + (roots.map (fun ζ => vmin p h ((progr t₀ d j : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    ← Finset.mul_sum, swap (range Y₀) roots (fun j ζ => vmin p h ((progr t₀ d j : K) - ζ))] at hsum
  have hV : (roots.map (fun ζ => ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ))).sum ≤
      (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1) + h) := by
    calc _ ≤ (roots.map (fun _ => (Y₀ : ℝ) / ((p : ℝ) - 1) + h)).sum :=
          Multiset.sum_map_le_sum_map _ _
            (fun ζ _ => (hC p K ζ t₀ d Y₀ h hd).trans (sumS p hp2 Y₀ h))
      _ = _ := by rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  have hDD : (∑ j ∈ range Y₀,
      ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤
      (roots.card : ℝ) := by
    have := hD p K roots t₀ d Y₀ h hd hYp
    exact_mod_cast this
  have hNc : (roots.card : ℝ) ≤ (del₀ : ℝ) * n₀ := by exact_mod_cast hcard
  have hN0 : (0 : ℝ) ≤ roots.card := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have h1 : (Y₀ : ℝ) * lam + (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1)) =
      (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1)) := by ring
  have h2 : (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1)) ≤ (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) :=
    mul_le_mul_of_nonneg_left hlam hY0.le
  have h3 : (roots.card : ℝ) * h ≤ (del₀ : ℝ) * n₀ * h := mul_le_mul_of_nonneg_right hNc hh0
  have h4 : E * (roots.card : ℝ) ≤ E * ((del₀ : ℝ) * n₀) := mul_le_mul_of_nonneg_left hNc hE.le
  have h5 : E * (∑ j ∈ range Y₀,
      ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤
      E * (roots.card : ℝ) := mul_le_mul_of_nonneg_left hDD hE.le
  have hS : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤
      (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀) := by
    nlinarith
  have eR : (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E) * Y₀ * E =
      (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀) := by
    field_simp
    ring
  rw [div_le_iff₀ hY0, ← mul_le_mul_iff_of_pos_right hE, eR]
  exact hS

theorem windowFullAP_of (hL : ValuationWindowLowerBound) (hW : WindowMeanAP) : WindowFullAP := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ d Y₀ La₀ U V dg hd hY hYp hdel hE hlead hc hdet hj hlam
  have hcard : roots.card ≤ del₀ * n := by
    have e : ((binMatK K del₀ c).det).natDegree = roots.card := by
      rw [hdet, natDegree_C_mul hlead, natDegree_multiset_prod_X_sub_C_eq_card]
    rw [← e]
    exact binMatK_det_natDegree_le K del₀ c
  refine hW p K roots (-Real.logb p ‖lead‖) La₀ E n del₀ t₀ d Y₀ h
    (fun t => (univ.filter (fun i => ‖dg t i‖ ≤ (p : ℝ) ^ (-E))).card) hd hY hYp hE hcard hlam ?_
  intro j hjr
  obtain ⟨hU, hV, hdU, hdV, hmap⟩ := hj j hjr
  exact hL p K n del₀ h E c lead roots (progr t₀ d j) (U (progr t₀ d j)) (V (progr t₀ d j))
    (dg (progr t₀ d j)) hc hU hV hdU hdV hE.le hdel hlead hdet hmap

end Formalism.GM
