import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.DotVecMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GeomQuarter

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

open TraceLipschitz GeometricWindowBounds

section GRLipPf

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem rho_nonneg' (x : ℝ) : 0 ≤ rho x := by
  unfold rho; exact Real.smoothTransition.nonneg _

private theorem rho_le_one' (x : ℝ) : rho x ≤ 1 := by
  unfold rho; exact Real.smoothTransition.le_one _

private theorem exists_abs_rho_sub_le_mul_abs_sub : ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, |rho x - rho y| ≤ K * |x - y| := by
  obtain ⟨K, hK⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
    (s := Set.Icc (0:ℝ) 1) one_ne_zero (convex_Icc 0 1) isCompact_Icc
  have hst : ∀ x : ℝ, Real.smoothTransition x = Real.smoothTransition (max 0 (min 1 x)) := by
    intro x
    rcases le_total x 0 with hx | hx
    · rw [max_eq_left (min_le_of_right_le hx)]
      rw [Real.smoothTransition.zero_of_nonpos hx, Real.smoothTransition.zero_of_nonpos le_rfl]
    rcases le_total 1 x with hx1 | hx1
    · rw [min_eq_left hx1, max_eq_right zero_le_one]
      rw [Real.smoothTransition.one_of_one_le hx1, Real.smoothTransition.one_of_one_le le_rfl]
    · rw [min_eq_right hx1, max_eq_right hx]
  have hmem : ∀ x : ℝ, max 0 (min 1 x) ∈ Set.Icc (0:ℝ) 1 :=
    fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hc : ∀ x y : ℝ, |max 0 (min 1 x) - max 0 (min 1 y)| ≤ |x - y| := by
    intro x y
    have h1 := abs_max_sub_max_le_abs (min 1 x) (min 1 y) 0
    have h2 : |min 1 x - min 1 y| ≤ |x - y| := abs_min_sub_min_le_max 1 x 1 y |>.trans (by simp)
    rw [max_comm 0 (min 1 x), max_comm 0 (min 1 y)]
    exact h1.trans h2
  refine ⟨K, K.2, fun x y => ?_⟩
  unfold rho
  rw [hst ((4 - x) / 3), hst ((4 - y) / 3)]
  have h := hK.dist_le_mul _ (hmem ((4 - x) / 3)) _ (hmem ((4 - y) / 3))
  rw [Real.dist_eq, Real.dist_eq] at h
  have h3 := hc ((4 - x) / 3) ((4 - y) / 3)
  have h4 : |(4 - x) / 3 - (4 - y) / 3| ≤ |x - y| := by
    rw [show (4 - x) / 3 - (4 - y) / 3 = (y - x) / 3 by ring, abs_div, abs_sub_comm]
    have : (0:ℝ) ≤ |x - y| := abs_nonneg _
    rw [abs_of_pos (by norm_num : (0:ℝ) < 3)]
    linarith
  calc _ ≤ (K:ℝ) * |max 0 (min 1 ((4 - x) / 3)) - max 0 (min 1 ((4 - y) / 3))| := h
    _ ≤ K * |x - y| := mul_le_mul_of_nonneg_left (h3.trans h4) K.2

private theorem pf_GRLip_lemma_2 (T : Finset ℤ) :
    ∀ m : ℤ, (∀ j ∈ T, j ≤ m) → ∑ j ∈ T, (4:ℝ) ^ j ≤ 4 / 3 * (4:ℝ) ^ m := by
  induction T using Finset.induction_on_max with
  | empty =>
    intro m _
    simp only [Finset.sum_empty]
    positivity
  | insert a s ha ih =>
    intro m hm
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert has]
    have h1 := ih (a - 1) (fun j hj => by have := ha j hj; omega)
    have h2 : (4:ℝ) ^ (a - 1) = (4:ℝ) ^ a / 4 := by
      rw [zpow_sub_one₀ (by norm_num : (4:ℝ) ≠ 0)]; ring
    have h3 : (4:ℝ) ^ a ≤ (4:ℝ) ^ m :=
      zpow_le_zpow_right₀ (by norm_num) (hm a (Finset.mem_insert_self a s))
    rw [h2] at h1
    linarith

private theorem pf_GRLip_lemma_3 (T : Finset ℤ) :
    ∀ m : ℤ, (∀ j ∈ T, m ≤ j) → ∑ j ∈ T, ((4:ℝ) ^ j)⁻¹ ≤ 4 / 3 * ((4:ℝ) ^ m)⁻¹ := by
  induction T using Finset.induction_on_min with
  | empty =>
    intro m _
    simp only [Finset.sum_empty]
    positivity
  | insert a s ha ih =>
    intro m hm
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert has]
    have h1 := ih (a + 1) (fun j hj => by have := ha j hj; omega)
    have h2 : ((4:ℝ) ^ (a + 1))⁻¹ = ((4:ℝ) ^ a)⁻¹ / 4 := by
      rw [zpow_add_one₀ (by norm_num : (4:ℝ) ≠ 0)]; field_simp
    have h3 : ((4:ℝ) ^ a)⁻¹ ≤ ((4:ℝ) ^ m)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact zpow_le_zpow_right₀ (by norm_num) (hm a (Finset.mem_insert_self a s))
    rw [h2] at h1
    linarith

private theorem pf_GRLip_lemma_6 (K Cm Ct c δ a b Q Q' lam lamD : ℝ) (S : Finset ℤ) (lo hi : ℤ)
    (r r' t t' : ℤ → ℝ) (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (hCt : 0 ≤ Ct) (hc : 0 < c)
    (hlam : 0 < lam) (hlamD : 0 < lamD) (ha : c * lamD ≤ a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1 / 4) (hQ : 0 ≤ Q) (hQQ : |Q' - Q| ≤ δ * Q)
    (hab : |b - a| ≤ Cm * δ * a)
    (hKr : ∀ j : ℤ, |r' j - r j| ≤ K * |(4:ℝ) ^ j * b - (4:ℝ) ^ j * a|)
    (hr : ∀ j : ℤ, 0 ≤ r j ∧ r j ≤ 1) (hr' : ∀ j : ℤ, 0 ≤ r' j ∧ r' j ≤ 1)
    (hr1 : ∀ j : ℤ, (4:ℝ) ^ j * a ≤ 1 → r j = 1) (hr1' : ∀ j : ℤ, (4:ℝ) ^ j * b ≤ 1 → r' j = 1)
    (ht : ∀ j : ℤ, 0 ≤ t j ∧ t j ≤ 4 / (4:ℝ) ^ j * Q)
    (ht' : ∀ j : ℤ, 0 ≤ t' j ∧ t' j ≤ 4 / (4:ℝ) ^ j * Q')
    (htt : ∀ j : ℤ, |t' j - t j| ≤ Ct * δ / (4:ℝ) ^ j * Q)
    (hlo : ∀ j ∈ S, lo ≤ j) (hlo' : 3 * lam / 64 < (4:ℝ) ^ lo)
    (hhi : ∀ j ∈ S, j ≤ hi) (hhi' : (4:ℝ) ^ hi * min a b ≤ 4) :
    |(b * Q' + ∑ j ∈ S, r' j * t' j) - (a * Q + ∑ j ∈ S, r j * t j)| ≤
      ((1 + 2 * Cm + 80 * K * Cm) + 2 * Cm * (3 + Cm) + Ct * 256 / (9 * c) + 2 * Cm * 256 / c) *
        (1 + (lam * lamD)⁻¹) * δ * (a * Q) := by
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hc hlamD) ha
  have hQQ' := abs_le.mp hQQ
  have hδQ : δ * Q ≤ 1 / 4 * Q := mul_le_mul_of_nonneg_right hδ4 hQ
  have hδQ0 : 0 ≤ δ * Q := mul_nonneg hδ hQ
  have hQ'0 : 0 ≤ Q' := by linarith [hQQ'.1]
  have hQ'5 : Q' ≤ 5 / 4 * Q := by linarith [hQQ'.2]
  have hE0 : 0 ≤ (lam * lamD)⁻¹ := by positivity
  have hQl : Q / lam ≤ a * Q * (lam * lamD)⁻¹ / c := by
    have h1 : a * Q * (lam * lamD)⁻¹ / c = Q / lam * (a / (c * lamD)) := by
      field_simp
    have h2 : 1 ≤ a / (c * lamD) := by rw [le_div_iff₀ (mul_pos hc hlamD)]; linarith
    rw [h1]
    have : 0 ≤ Q / lam := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 this
    linarith
  have hG : ∑ j ∈ S, ((4:ℝ) ^ j)⁻¹ ≤ 256 / (9 * lam) := by
    have h1 := pf_GRLip_lemma_3 S lo hlo
    have h2 : ((4:ℝ) ^ lo)⁻¹ ≤ 64 / (3 * lam) := by
      rw [← inv_div]
      exact inv_anti₀ (by positivity) (by linarith)
    calc _ ≤ 4 / 3 * ((4:ℝ) ^ lo)⁻¹ := h1
      _ ≤ 4 / 3 * (64 / (3 * lam)) := by gcongr
      _ = 256 / (9 * lam) := by field_simp; ring
  have hsplit : (b * Q' + ∑ j ∈ S, r' j * t' j) - (a * Q + ∑ j ∈ S, r j * t j) =
      ((b - a) * Q' + a * (Q' - Q)) + ∑ j ∈ S, ((r' j - r j) * t' j + r j * (t' j - t j)) := by
    have : ∑ j ∈ S, r' j * t' j - ∑ j ∈ S, r j * t j =
        ∑ j ∈ S, ((r' j - r j) * t' j + r j * (t' j - t j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    linarith
  have hB : ∀ j, r j * |t' j - t j| ≤ Ct * δ * Q * ((4:ℝ) ^ j)⁻¹ := by
    intro j
    have h4 : 0 < (4:ℝ) ^ j := zpow_pos (by norm_num) j
    calc r j * |t' j - t j| ≤ 1 * |t' j - t j| :=
          mul_le_mul_of_nonneg_right (hr j).2 (abs_nonneg _)
      _ ≤ Ct * δ / (4:ℝ) ^ j * Q := by rw [one_mul]; exact htt j
      _ = Ct * δ * Q * ((4:ℝ) ^ j)⁻¹ := by field_simp
  have hT : ∀ j, t j ≤ 4 * Q * ((4:ℝ) ^ j)⁻¹ := by
    intro j; have := (ht j).2; rw [div_eq_mul_inv] at this; linarith
  have hT' : ∀ j, t' j ≤ 4 * Q' * ((4:ℝ) ^ j)⁻¹ := by
    intro j; have := (ht' j).2; rw [div_eq_mul_inv] at this; linarith
  rw [hsplit]
  set C0 := (1 + 2 * Cm + 80 * K * Cm) + 2 * Cm * (3 + Cm) + Ct * 256 / (9 * c) + 2 * Cm * 256 / c
    with hC0
  have hc1 : 0 ≤ 1 + 2 * Cm + 80 * K * Cm := by positivity
  have hc2 : 0 ≤ 2 * Cm * (3 + Cm) := by positivity
  have hc3 : 0 ≤ Ct * 256 / (9 * c) := by positivity
  have hc4 : 0 ≤ 2 * Cm * 256 / c := by positivity
  have haQ : 0 ≤ a * Q := by positivity
  have hRHS : C0 * (1 + (lam * lamD)⁻¹) * δ * (a * Q) =
      C0 * δ * (a * Q) + C0 * δ * (a * Q * (lam * lamD)⁻¹) := by ring
  rw [hRHS]
  rcases le_or_gt (Cm * δ) (1 / 2) with hs | hl
  · have hba : |b - a| ≤ a / 2 := by nlinarith
    have hba' := abs_le.mp hba
    have hmin : a / 2 ≤ min a b := le_min (by linarith) (by linarith)
    have hhia : (4:ℝ) ^ hi * a ≤ 8 := by
      have h4 : 0 < (4:ℝ) ^ hi := zpow_pos (by norm_num) hi
      have := mul_le_mul_of_nonneg_left hmin h4.le
      linarith
    have hA : ∀ j, |r' j - r j| * t' j ≤ 6 * K * |b - a| * Q' * a * (4:ℝ) ^ j := by
      intro j
      have h4 : 0 < (4:ℝ) ^ j := zpow_pos (by norm_num) j
      by_cases hj : (4:ℝ) ^ j * (3 / 2 * a) ≤ 1
      · have e1 : r j = 1 := hr1 j
          (le_trans (mul_le_mul_of_nonneg_left (by linarith) h4.le) hj)
        have e2 : r' j = 1 := hr1' j
          (le_trans (mul_le_mul_of_nonneg_left (by linarith [hba'.2]) h4.le) hj)
        rw [e1, e2, sub_self, abs_zero, zero_mul]
        positivity
      · push_neg at hj
        have k1 : |r' j - r j| ≤ K * ((4:ℝ) ^ j * |b - a|) := by
          have := hKr j
          rwa [← mul_sub, abs_mul, abs_of_pos h4] at this
        calc |r' j - r j| * t' j ≤ K * ((4:ℝ) ^ j * |b - a|) * (4 * Q' * ((4:ℝ) ^ j)⁻¹) :=
              mul_le_mul k1 (hT' j) (ht' j).1 (by positivity)
          _ = 4 * K * |b - a| * Q' := by field_simp
          _ ≤ 4 * K * |b - a| * Q' * ((4:ℝ) ^ j * (3 / 2 * a)) :=
              le_mul_of_one_le_right (by positivity) hj.le
          _ = 6 * K * |b - a| * Q' * a * (4:ℝ) ^ j := by ring
    have hSA : ∑ j ∈ S, |r' j - r j| * t' j ≤ 64 * K * |b - a| * Q' := by
      calc ∑ j ∈ S, |r' j - r j| * t' j ≤ ∑ j ∈ S, 6 * K * |b - a| * Q' * a * (4:ℝ) ^ j :=
            Finset.sum_le_sum (fun j _ => hA j)
        _ = 6 * K * |b - a| * Q' * a * ∑ j ∈ S, (4:ℝ) ^ j := by rw [Finset.mul_sum]
        _ ≤ 6 * K * |b - a| * Q' * a * (4 / 3 * (4:ℝ) ^ hi) := by
            gcongr
            exact pf_GRLip_lemma_2 S hi hhi
        _ = 8 * K * |b - a| * Q' * ((4:ℝ) ^ hi * a) := by ring
        _ ≤ 8 * K * |b - a| * Q' * 8 := by gcongr
        _ = 64 * K * |b - a| * Q' := by ring
    have hSB : ∑ j ∈ S, r j * |t' j - t j| ≤ Ct * δ * Q * (256 / (9 * lam)) := by
      calc ∑ j ∈ S, r j * |t' j - t j| ≤ ∑ j ∈ S, Ct * δ * Q * ((4:ℝ) ^ j)⁻¹ :=
            Finset.sum_le_sum (fun j _ => hB j)
        _ = Ct * δ * Q * ∑ j ∈ S, ((4:ℝ) ^ j)⁻¹ := by rw [Finset.mul_sum]
        _ ≤ Ct * δ * Q * (256 / (9 * lam)) := by gcongr
    have hsum : |∑ j ∈ S, ((r' j - r j) * t' j + r j * (t' j - t j))| ≤
        64 * K * |b - a| * Q' + Ct * δ * Q * (256 / (9 * lam)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ S, |(r' j - r j) * t' j + r j * (t' j - t j)| ≤
            ∑ j ∈ S, (|r' j - r j| * t' j + r j * |t' j - t j|) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_of_nonneg (ht' j).1, abs_of_nonneg (hr j).1]
        _ = ∑ j ∈ S, |r' j - r j| * t' j + ∑ j ∈ S, r j * |t' j - t j| := Finset.sum_add_distrib
        _ ≤ _ := add_le_add hSA hSB
    have hfirst : |(b - a) * Q' + a * (Q' - Q)| ≤ |b - a| * Q' + a * (δ * Q) := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg hQ'0]
      · rw [abs_mul, abs_of_pos ha0]
        exact mul_le_mul_of_nonneg_left hQQ ha0.le
    have hbaQ : |b - a| * Q' ≤ Cm * δ * a * (5 / 4 * Q) :=
      mul_le_mul hab hQ'5 hQ'0 (by positivity)
    have hKb : 64 * K * |b - a| * Q' ≤ 80 * K * Cm * δ * (a * Q) := by
      have := mul_le_mul_of_nonneg_left hbaQ (by positivity : (0:ℝ) ≤ 64 * K)
      linarith
    have hCtQ : Ct * δ * Q * (256 / (9 * lam)) ≤ Ct * 256 / (9 * c) * δ * (a * Q * (lam * lamD)⁻¹) := by
      have e : Ct * δ * Q * (256 / (9 * lam)) = Ct * 256 / 9 * δ * (Q / lam) := by
        field_simp
      have e2 : Ct * 256 / (9 * c) * δ * (a * Q * (lam * lamD)⁻¹) =
          Ct * 256 / 9 * δ * (a * Q * (lam * lamD)⁻¹ / c) := by
        field_simp
      rw [e, e2]
      gcongr
    have hX : C0 * δ * (a * Q) ≥ (1 + 2 * Cm + 80 * K * Cm) * δ * (a * Q) := by
      apply mul_le_mul_of_nonneg_right _ haQ
      apply mul_le_mul_of_nonneg_right _ hδ
      rw [hC0]; linarith
    have hY : C0 * δ * (a * Q * (lam * lamD)⁻¹) ≥ Ct * 256 / (9 * c) * δ * (a * Q * (lam * lamD)⁻¹) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hδ
      rw [hC0]; linarith
    have hδaQ : 0 ≤ δ * (a * Q) := by positivity
    calc _ ≤ |(b - a) * Q' + a * (Q' - Q)| + |∑ j ∈ S, ((r' j - r j) * t' j + r j * (t' j - t j))| :=
          abs_add_le _ _
      _ ≤ (Cm * δ * a * (5 / 4 * Q) + a * (δ * Q)) +
          (80 * K * Cm * δ * (a * Q) + Ct * 256 / (9 * c) * δ * (a * Q * (lam * lamD)⁻¹)) := by
          linarith
      _ ≤ _ := by
          have hm : (5 / 4 * Cm + 1 + 80 * K * Cm) * (δ * (a * Q)) ≤
              (1 + 2 * Cm + 80 * K * Cm) * (δ * (a * Q)) :=
            mul_le_mul_of_nonneg_right (by linarith) hδaQ
          linarith
  · have hbb : b ≤ a * (1 + Cm / 4) := by
      have h1 := (abs_le.mp hab).2
      have h2 : Cm * δ ≤ Cm * (1 / 4) := mul_le_mul_of_nonneg_left hδ4 hCm
      have h3 := mul_le_mul_of_nonneg_right h2 ha0.le
      linarith
    have hsum : |∑ j ∈ S, ((r' j - r j) * t' j + r j * (t' j - t j))| ≤ 9 * Q * (256 / (9 * lam)) := by
      have e : ∑ j ∈ S, ((r' j - r j) * t' j + r j * (t' j - t j)) =
          ∑ j ∈ S, r' j * t' j - ∑ j ∈ S, r j * t j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have s1 : ∑ j ∈ S, r' j * t' j ≤ 5 * Q * (256 / (9 * lam)) := by
        calc ∑ j ∈ S, r' j * t' j ≤ ∑ j ∈ S, 5 * Q * ((4:ℝ) ^ j)⁻¹ := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              have h4 : 0 ≤ ((4:ℝ) ^ j)⁻¹ := by positivity
              have m1 : r' j * t' j ≤ t' j := mul_le_of_le_one_left (ht' j).1 (hr' j).2
              have m2 : 4 * Q' * ((4:ℝ) ^ j)⁻¹ ≤ 5 * Q * ((4:ℝ) ^ j)⁻¹ :=
                mul_le_mul_of_nonneg_right (by linarith) h4
              linarith [hT' j]
          _ = 5 * Q * ∑ j ∈ S, ((4:ℝ) ^ j)⁻¹ := by rw [Finset.mul_sum]
          _ ≤ 5 * Q * (256 / (9 * lam)) := by gcongr
      have s2 : ∑ j ∈ S, r j * t j ≤ 4 * Q * (256 / (9 * lam)) := by
        calc ∑ j ∈ S, r j * t j ≤ ∑ j ∈ S, 4 * Q * ((4:ℝ) ^ j)⁻¹ := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              have m1 : r j * t j ≤ t j := mul_le_of_le_one_left (ht j).1 (hr j).2
              linarith [hT j]
          _ = 4 * Q * ∑ j ∈ S, ((4:ℝ) ^ j)⁻¹ := by rw [Finset.mul_sum]
          _ ≤ 4 * Q * (256 / (9 * lam)) := by gcongr
      have s3 : 0 ≤ ∑ j ∈ S, r' j * t' j :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hr' j).1 (ht' j).1)
      have s4 : 0 ≤ ∑ j ∈ S, r j * t j :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hr j).1 (ht j).1)
      rw [e, abs_le]
      constructor <;> linarith
    have hfirst : |(b - a) * Q' + a * (Q' - Q)| ≤ (3 + Cm) * (a * Q) := by
      have e : (b - a) * Q' + a * (Q' - Q) = b * Q' - a * Q := by ring
      rw [e, abs_le]
      have h1 : b * Q' ≤ a * (1 + Cm / 4) * (5 / 4 * Q) := mul_le_mul hbb hQ'5 hQ'0 (by positivity)
      have h2 : 0 ≤ b * Q' := mul_nonneg hb.le hQ'0
      have h3 : 0 ≤ Cm * (a * Q) := mul_nonneg hCm haQ
      constructor <;> linarith
    have hQl' : 9 * Q * (256 / (9 * lam)) ≤ 256 / c * (a * Q * (lam * lamD)⁻¹) := by
      have e : 9 * Q * (256 / (9 * lam)) = 256 * (Q / lam) := by field_simp
      have e2 : 256 / c * (a * Q * (lam * lamD)⁻¹) = 256 * (a * Q * (lam * lamD)⁻¹ / c) := by
        field_simp
      rw [e, e2]
      linarith
    have h2C : 1 ≤ 2 * Cm * δ := by linarith
    have hZ : 0 ≤ a * Q * (lam * lamD)⁻¹ := by positivity
    have hX : C0 * δ ≥ 2 * Cm * (3 + Cm) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ; rw [hC0]; linarith
    have hY : C0 * δ ≥ 2 * Cm * 256 / c * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ; rw [hC0]; linarith
    have hW1 : (3 + Cm) * (a * Q) ≤ C0 * δ * (a * Q) := by
      calc (3 + Cm) * (a * Q) ≤ (3 + Cm) * (2 * Cm * δ) * (a * Q) := by
            have : (3 + Cm) * 1 ≤ (3 + Cm) * (2 * Cm * δ) :=
              mul_le_mul_of_nonneg_left h2C (by positivity)
            have := mul_le_mul_of_nonneg_right this haQ
            linarith
        _ = 2 * Cm * (3 + Cm) * δ * (a * Q) := by ring
        _ ≤ C0 * δ * (a * Q) := mul_le_mul_of_nonneg_right hX haQ
    have hW2 : 256 / c * (a * Q * (lam * lamD)⁻¹) ≤ C0 * δ * (a * Q * (lam * lamD)⁻¹) := by
      calc 256 / c * (a * Q * (lam * lamD)⁻¹) ≤ 256 / c * (2 * Cm * δ) * (a * Q * (lam * lamD)⁻¹) := by
            have : 256 / c * 1 ≤ 256 / c * (2 * Cm * δ) :=
              mul_le_mul_of_nonneg_left h2C (by positivity)
            have := mul_le_mul_of_nonneg_right this hZ
            linarith
        _ = 2 * Cm * 256 / c * δ * (a * Q * (lam * lamD)⁻¹) := by ring
        _ ≤ C0 * δ * (a * Q * (lam * lamD)⁻¹) := mul_le_mul_of_nonneg_right hY hZ
    calc _ ≤ |(b - a) * Q' + a * (Q' - Q)| + |∑ j ∈ S, ((r' j - r j) * t' j + r j * (t' j - t j))| :=
          abs_add_le _ _
      _ ≤ (3 + Cm) * (a * Q) + 256 / c * (a * Q * (lam * lamD)⁻¹) := by linarith
      _ ≤ _ := by linarith

private theorem pf_GRLip_lemma_4 (h k : HS L N) (z : VR L N) : qR (h + k) z = qR h z + qR k z := by
  unfold qR mat
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [Submodule.coe_add, Pi.add_apply, ← Matrix.of_add_of, Matrix.add_mulVec, dotProduct_add,
    Complex.add_re]

private theorem pf_GRLip_lemma_5 (c : ℝ) (h : HS L N) (z : VR L N) : qR (c • h) z = c * qR h z := by
  unfold qR mat
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [Submodule.coe_smul, Pi.smul_apply, ← Matrix.smul_of, Matrix.smul_mulVec, dotProduct_smul,
    Complex.smul_re, smul_eq_mul]

private theorem pf_GRLip_lemma_7 (μ : HS L N → ℝ) (g : HS L N) (z : VR L N) (S : Finset ℤ)
    (hsup : ∀ j : ℤ, j ∉ S → rho ((4:ℝ) ^ j * μ g) • term ((4:ℝ) ^ j) g = 0) :
    qR (ret μ g) z = μ g * qR g z + ∑ j ∈ S, rho ((4:ℝ) ^ j * μ g) * qR (term ((4:ℝ) ^ j) g) z := by
  let F : HS L N →+ ℝ := AddMonoidHom.mk' (fun x => qR x z) (fun x y => pf_GRLip_lemma_4 x y z)
  have hs : Function.support (fun j : ℤ => rho ((4:ℝ) ^ j * μ g) • term ((4:ℝ) ^ j) g) ⊆ ↑S := by
    intro j hj
    by_contra hn
    exact hj (hsup j hn)
  unfold ret
  rw [pf_GRLip_lemma_4, pf_GRLip_lemma_5]
  congr 1
  have h1 : qR (∑ᶠ j : ℤ, rho ((4:ℝ) ^ j * μ g) • term ((4:ℝ) ^ j) g) z =
      F (∑ᶠ j : ℤ, rho ((4:ℝ) ^ j * μ g) • term ((4:ℝ) ^ j) g) := rfl
  rw [h1, map_finsum F (S.finite_toSet.subset hs)]
  rw [finsum_eq_sum_of_support_subset _ (fun j hj => hs (fun h0 => hj (by
    have h0' : rho ((4:ℝ) ^ j * μ g) • term ((4:ℝ) ^ j) g = 0 := h0
    rw [h0']
    exact map_zero F)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact pf_GRLip_lemma_5 _ _ z

set_option maxHeartbeats 1000000 in
theorem pf_GRLip : GRLip := by
  intro hB hR hT
  unfold Basic at hB
  unfold REqv at hR
  unfold TLip at hT
  unfold RLip
  intro L₁ _ _ N₁ hN μ hμ
  obtain ⟨CT, hCT⟩ := hT L₁ N₁ hN
  have hB1 := hB L₁ N₁ hN
  have hR1 := hR L₁ N₁ hN μ hμ
  obtain ⟨-, -, ⟨c, Cu, hc, hcC⟩, ⟨Cμ, hCμ⟩⟩ := hμ
  obtain ⟨K, hK0, hK⟩ := exists_abs_rho_sub_le_mul_abs_sub
  have hCn : 0 ≤ (1 + 2 * |Cμ| + 80 * K * |Cμ|) + 2 * |Cμ| * (3 + |Cμ|) + |CT| * 256 / (9 * c) +
      2 * |Cμ| * 256 / c := by
    have h1 : 0 ≤ |CT| * 256 / (9 * c) := div_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ 2 * |Cμ| * 256 / c := div_nonneg (by positivity) hc.le
    have h3 : 0 ≤ 80 * K * |Cμ| := by positivity
    have h4 : 0 ≤ 2 * |Cμ| * (3 + |Cμ|) := by positivity
    have h5 : 0 ≤ |Cμ| := abs_nonneg _
    linarith
  refine ⟨_, hCn, ?_⟩
  intro δ hδ0 hδ4 h hh k hk
  have hkP : k ∈ Pos L₁ N₁ := (hB1.2.2.2.1 δ hδ0 (by linarith) h hh k hk).1
  have hlamP : ∀ g ∈ Pos L₁ N₁, 0 < lam g := fun g hg => (hB1.1 g hg).1
  have hlamDP : ∀ g ∈ Pos L₁ N₁, 0 < lamD g := fun g hg => by
    have e : lamD g = lam (dualH g) := rfl
    rw [e]
    exact hlamP _ (hB1.1 g hg).2.2.2.1
  have hμP : ∀ g ∈ Pos L₁ N₁, 0 < μ g := fun g hg =>
    lt_of_lt_of_le (mul_pos hc (hlamDP g hg)) (hcC g hg).1
  have hlamk : 3 / 4 * lam h ≤ lam k := by
    obtain ⟨v0, hv0, -⟩ := (hB1.1 h hh).2.2.1
    unfold lam
    haveI : Nonempty {v : UpperTheory.V.KT.Lat L₁ N₁ // v ≠ 0} := ⟨⟨v0, hv0⟩⟩
    apply le_ciInf
    intro y
    have e1 : lam h ≤ q h y := (hB1.1 h hh).2.1 y y.2
    have e2 := hk (toR (y : UpperTheory.V.KT.Lat L₁ N₁))
    have e3 : q k y = qR k (toR (y : UpperTheory.V.KT.Lat L₁ N₁)) := rfl
    have e4 : q h y = qR h (toR (y : UpperTheory.V.KT.Lat L₁ N₁)) := rfl
    have e5 := hlamP h hh
    rw [abs_le] at e2
    have e6 : lam h = ⨅ y : {v : UpperTheory.V.KT.Lat L₁ N₁ // v ≠ 0}, q h y := rfl
    rw [← e6]
    nlinarith
  have hlamh := hlamP h hh
  have hah := hμP h hh
  have hbk := hμP k hkP
  set lo : ℤ := Int.log 4 (3 * lam h / 16) with hlo_def
  set hi : ℤ := max (Int.log 4 (4 / μ h)) (Int.log 4 (4 / μ k)) with hhi_def
  have hlo' : 3 * lam h / 64 < (4:ℝ) ^ lo := by
    have e := Int.lt_zpow_succ_log_self (R := ℝ) (b := 4) (by norm_num) (3 * lam h / 16)
    rw [zpow_add_one₀ (by norm_num)] at e
    push_cast at e
    linarith
  have hlo2 : (4:ℝ) ^ lo ≤ 3 * lam h / 16 := by
    have e := Int.zpow_log_le_self (R := ℝ) (b := 4) (by norm_num) (by positivity : 0 < 3 * lam h / 16)
    push_cast at e
    exact e
  have hA : ∀ x : ℝ, 0 < x → ∀ j : ℤ, Int.log 4 (4 / x) < j → 4 < (4:ℝ) ^ j * x := by
    intro x hx j hj
    have e := Int.lt_zpow_succ_log_self (R := ℝ) (b := 4) (by norm_num) (4 / x)
    push_cast at e
    have e2 : (4:ℝ) ^ (Int.log 4 (4 / x) + 1) ≤ (4:ℝ) ^ j := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have e3 : 4 / x < (4:ℝ) ^ j := lt_of_lt_of_le e e2
    rwa [div_lt_iff₀ hx] at e3
  have hrho0 : ∀ x : ℝ, 4 ≤ x → rho x = 0 := by
    intro x hx
    unfold rho
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hrho1 : ∀ x : ℝ, x ≤ 1 → rho x = 1 := by
    intro x hx
    unfold rho
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hsup : ∀ g ∈ Pos L₁ N₁, 3 / 4 * lam h ≤ lam g → Int.log 4 (4 / μ g) ≤ hi →
      ∀ j : ℤ, j ∉ Finset.Icc lo hi → rho ((4:ℝ) ^ j * μ g) • term ((4:ℝ) ^ j) g = 0 := by
    intro g hg hlg hgi j hj
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with hj | hj
    · have e1 : (4:ℝ) ^ (j + 1) ≤ (4:ℝ) ^ lo := zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add_one₀ (by norm_num)] at e1
      have e2 : 4 * (4:ℝ) ^ j ≤ lam g := by linarith
      rw [((hCT ((4:ℝ) ^ j) (by positivity) g hg 0).2.1 e2), smul_zero]
    · rw [hrho0 _ (hA _ (hμP g hg) j (by omega)).le, zero_smul]
  have hret : ∀ g ∈ Pos L₁ N₁, 3 / 4 * lam h ≤ lam g → Int.log 4 (4 / μ g) ≤ hi → ∀ z : VR L₁ N₁,
      qR (ret μ g) z = μ g * qR g z + ∑ j ∈ Finset.Icc lo hi,
        rho ((4:ℝ) ^ j * μ g) * qR (term ((4:ℝ) ^ j) g) z :=
    fun g hg hlg hgi z => pf_GRLip_lemma_7 μ g z _ (hsup g hg hlg hgi)
  have hhi' : (4:ℝ) ^ hi * min (μ h) (μ k) ≤ 4 := by
    have eA : ∀ x : ℝ, 0 < x → (4:ℝ) ^ Int.log 4 (4 / x) * x ≤ 4 := by
      intro x hx
      have e := Int.zpow_log_le_self (R := ℝ) (b := 4) (by norm_num) (by positivity : 0 < 4 / x)
      push_cast at e
      rwa [le_div_iff₀ hx] at e
    rcases le_total (Int.log 4 (4 / μ h)) (Int.log 4 (4 / μ k)) with hle | hle
    · rw [hhi_def, max_eq_right hle]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans (eA _ hbk)
    · rw [hhi_def, max_eq_left hle]
      exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans (eA _ hah)
  unfold Cl
  intro z
  rw [hret k hkP hlamk (le_max_right _ _) z, hret h hh (by linarith) (le_max_left _ _) z]
  have hQ : 0 ≤ qR h z := by
    have e := (hCT 1 one_pos h hh z).1
    linarith [e.1, e.2]
  have hab : |μ k - μ h| ≤ |Cμ| * δ * μ h := by
    refine (hCμ δ hδ0 hδ4 h hh k hk).trans ?_
    have : Cμ ≤ |Cμ| := le_abs_self _
    have : 0 ≤ δ * μ h := by positivity
    nlinarith
  have key := pf_GRLip_lemma_6 K |Cμ| |CT| c δ (μ h) (μ k) (qR h z) (qR k z) (lam h) (lamD h)
    (Finset.Icc lo hi) lo hi
    (fun j => rho ((4:ℝ) ^ j * μ h)) (fun j => rho ((4:ℝ) ^ j * μ k))
    (fun j => qR (term ((4:ℝ) ^ j) h) z) (fun j => qR (term ((4:ℝ) ^ j) k) z)
    hK0 (abs_nonneg _) (abs_nonneg _) hc hlamh (hlamDP h hh) (hcC h hh).1 hbk hδ0 hδ4 hQ (hk z) hab
    (fun j => hK _ _)
    (fun j => ⟨rho_nonneg' _, rho_le_one' _⟩) (fun j => ⟨rho_nonneg' _, rho_le_one' _⟩)
    (fun j hj => hrho1 _ hj) (fun j hj => hrho1 _ hj)
    (fun j => (hCT _ (by positivity) h hh z).1) (fun j => (hCT _ (by positivity) k hkP z).1)
    (fun j => by
      refine ((hCT _ (by positivity) h hh z).2.2 δ hδ0 hδ4 k hk).trans ?_
      have : CT ≤ |CT| := le_abs_self _
      have : 0 ≤ δ / (4:ℝ) ^ j * qR h z := by positivity
      calc CT * δ / (4:ℝ) ^ j * qR h z = CT * (δ / (4:ℝ) ^ j * qR h z) := by ring
        _ ≤ |CT| * (δ / (4:ℝ) ^ j * qR h z) := mul_le_mul_of_nonneg_right (le_abs_self _) this
        _ = |CT| * δ / (4:ℝ) ^ j * qR h z := by ring)
    (fun j hj => (Finset.mem_Icc.mp hj).1) hlo' (fun j hj => (Finset.mem_Icc.mp hj).2) hhi'
  refine key.trans ?_
  have hR2 := (hR1 h hh).2.2 z
  have hcoef : 0 ≤ ((1 + 2 * |Cμ| + 80 * K * |Cμ|) + 2 * |Cμ| * (3 + |Cμ|) + |CT| * 256 / (9 * c) +
      2 * |Cμ| * 256 / c) * (1 + (lam h * lamD h)⁻¹) * δ := by
    have : 0 ≤ (lam h * lamD h)⁻¹ := inv_nonneg.mpr (mul_pos hlamh (hlamDP h hh)).le
    have : 0 ≤ 1 + (lam h * lamD h)⁻¹ := by linarith
    positivity
  rw [← hret h hh (by linarith) (le_max_left _ _) z]
  exact mul_le_mul_of_nonneg_left hR2 hcoef

end GRLipPf

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
