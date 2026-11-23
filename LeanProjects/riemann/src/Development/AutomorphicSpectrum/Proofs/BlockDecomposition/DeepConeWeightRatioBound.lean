import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin.Ratio

def ext {r : ℕ} (t : Fin r → ℝ) (n : ℕ) : ℝ := if h : n < r then t ⟨n, h⟩ else 1

theorem ext_of_lt {r : ℕ} (t : Fin r → ℝ) {n : ℕ} (h : n < r) : ext t n = t ⟨n, h⟩ := dif_pos h

theorem ext_of_ge {r : ℕ} (t : Fin r → ℝ) {n : ℕ} (h : r ≤ n) : ext t n = 1 := dif_neg (not_lt.mpr h)

def bnd (r : ℕ) (c t₁ : ℝ) : ℝ := max ((t₁ / (min c 1) ^ r) ^ r) (((min c 1)⁻¹) ^ r)

variable {r : ℕ} {c t₁ : ℝ} {t : Fin r → ℝ}

theorem ext_pos (ht : t ∈ cone r c) (n : ℕ) : 0 < ext t n := by
  unfold ext; split_ifs with h
  · exact ht.1 _
  · exact one_pos

theorem ext_step (ht : t ∈ cone r c) {j : ℕ} (hj : j < r) : c * ext t (j + 1) ≤ ext t j := by
  rw [ext_of_lt t hj]
  by_cases h : j + 1 < r
  · rw [ext_of_lt t h]
    exact ht.2.1 ⟨j, hj⟩ ⟨j + 1, h⟩ rfl
  · rw [ext_of_ge t (by omega), mul_one]
    exact ht.2.2 ⟨j, hj⟩ (by show j + 1 = r; omega)

theorem ext_lower (hc : 0 < c) (ht : t ∈ cone r c) (n : ℕ) : (min c 1) ^ r ≤ ext t n := by
  have hc' : 0 < min c 1 := lt_min hc one_pos
  have hc1 : min c 1 ≤ 1 := min_le_right _ _
  have key : ∀ k n, n + k = r → (min c 1) ^ k ≤ ext t n := by
    intro k
    induction k with
    | zero => intro n hn; rw [pow_zero, ext_of_ge t (by omega)]
    | succ k ih =>
      intro n hn
      have h1 := ih (n + 1) (by omega)
      have h2 := ext_step ht (j := n) (by omega)
      have h3 : min c 1 * ext t (n + 1) ≤ c * ext t (n + 1) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (ext_pos ht _).le
      calc (min c 1) ^ (k + 1) = min c 1 * (min c 1) ^ k := by ring
        _ ≤ min c 1 * ext t (n + 1) := mul_le_mul_of_nonneg_left h1 hc'.le
        _ ≤ _ := h3.trans h2
  by_cases hn : n ≤ r
  · calc (min c 1) ^ r ≤ (min c 1) ^ (r - n) := pow_le_pow_of_le_one hc'.le hc1 (by omega)
      _ ≤ _ := key (r - n) n (by omega)
  · rw [ext_of_ge t (by omega)]; exact pow_le_one₀ hc'.le hc1

theorem ext_up (hc : 0 < c) (ht : t ∈ cone r c) {j : ℕ} (hj : j < r) :
    ext t (j + 1) ≤ (min c 1)⁻¹ * ext t j := by
  have hc' : 0 < min c 1 := lt_min hc one_pos
  rw [le_inv_mul_iff₀ hc']
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (ext_pos ht _).le).trans (ext_step ht hj)

theorem ext_nondeep (hc : 0 < c) (ht1 : 1 ≤ t₁) (ht : t ∈ cone r c) {j : ℕ} (hj : j < r)
    (hS : (⟨j, hj⟩ : Fin r) ∉ deep t₁ t) : ext t j ≤ t₁ / (min c 1) ^ r * ext t (j + 1) := by
  have hc' : 0 < min c 1 := lt_min hc one_pos
  have hp : 0 < (min c 1) ^ r := pow_pos hc' r
  have hp1 : (min c 1) ^ r ≤ 1 := pow_le_one₀ hc'.le (min_le_right _ _)
  have hlow := ext_lower hc ht (j + 1)
  have hR : t₁ ≤ t₁ / (min c 1) ^ r := by rw [le_div_iff₀ hp]; nlinarith
  simp only [deep, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall, not_lt] at hS
  rw [ext_of_lt t hj]
  by_cases h : t₁ < t ⟨j, hj⟩
  · obtain ⟨j', hj', hle⟩ := hS h
    have e : ext t (j + 1) = t j' := by
      rw [ext_of_lt t (show j + 1 < r by rw [← hj']; exact j'.isLt)]
      congr 1; ext; exact hj'.symm
    rw [e]
    calc t ⟨j, hj⟩ ≤ t₁ * t j' := hle
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (ht.1 j').le
  · push_neg at h
    calc t ⟨j, hj⟩ ≤ t₁ := h
      _ = t₁ / (min c 1) ^ r * (min c 1) ^ r := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (div_nonneg (by linarith) hp.le)

theorem ext_chain (hc : 0 < c) (ht1 : 1 ≤ t₁) (ht : t ∈ cone r c) (i : ℕ) :
    ∀ k, i + k ≤ r → (∀ j (hj : j < r), i ≤ j → j < i + k → (⟨j, hj⟩ : Fin r) ∉ deep t₁ t) →
    ext t i ≤ (t₁ / (min c 1) ^ r) ^ k * ext t (i + k) ∧
      ext t (i + k) ≤ ((min c 1)⁻¹) ^ k * ext t i := by
  have hc' : 0 < min c 1 := lt_min hc one_pos
  have hR0 : 0 ≤ t₁ / (min c 1) ^ r := div_nonneg (by linarith) (pow_pos hc' r).le
  intro k
  induction k with
  | zero => intro _ _; simp
  | succ k ih =>
    intro hk hS
    obtain ⟨h1, h2⟩ := ih (by omega) (fun j hj a b => hS j hj a (by omega))
    have s1 := ext_nondeep hc ht1 ht (j := i + k) (by omega) (hS (i + k) (by omega) (by omega) (by omega))
    have s2 := ext_up hc ht (j := i + k) (by omega)
    show ext t i ≤ (t₁ / (min c 1) ^ r) ^ (k + 1) * ext t (i + k + 1) ∧
      ext t (i + k + 1) ≤ ((min c 1)⁻¹) ^ (k + 1) * ext t i
    constructor
    · calc ext t i ≤ (t₁ / (min c 1) ^ r) ^ k * ext t (i + k) := h1
        _ ≤ (t₁ / (min c 1) ^ r) ^ k * (t₁ / (min c 1) ^ r * ext t (i + k + 1)) :=
          mul_le_mul_of_nonneg_left s1 (pow_nonneg hR0 _)
        _ = _ := by ring
    · calc ext t (i + k + 1) ≤ (min c 1)⁻¹ * ext t (i + k) := s2
        _ ≤ (min c 1)⁻¹ * (((min c 1)⁻¹) ^ k * ext t i) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hc'.le)
        _ = _ := by ring

theorem one_le_bnd (hc : 0 < c) (ht1 : 1 ≤ t₁) : 1 ≤ bnd r c t₁ := by
  have hc' : 0 < min c 1 := lt_min hc one_pos
  have hi : 1 ≤ (min c 1)⁻¹ := one_le_inv₀ hc' |>.mpr (min_le_right _ _)
  exact le_max_of_le_right (one_le_pow₀ hi)

theorem ext_bnd (hc : 0 < c) (ht1 : 1 ≤ t₁) (ht : t ∈ cone r c) {i l : ℕ} (hil : i ≤ l) (hl : l ≤ r)
    (hS : ∀ j (hj : j < r), i ≤ j → j < l → (⟨j, hj⟩ : Fin r) ∉ deep t₁ t) :
    ext t i ≤ bnd r c t₁ * ext t l ∧ ext t l ≤ bnd r c t₁ * ext t i := by
  have hc' : 0 < min c 1 := lt_min hc one_pos
  have hp : 0 < (min c 1) ^ r := pow_pos hc' r
  have hp1 : (min c 1) ^ r ≤ 1 := pow_le_one₀ hc'.le (min_le_right _ _)
  have hR1 : 1 ≤ t₁ / (min c 1) ^ r := by rw [le_div_iff₀ hp]; nlinarith
  have hi : 1 ≤ (min c 1)⁻¹ := one_le_inv₀ hc' |>.mpr (min_le_right _ _)
  obtain ⟨h1, h2⟩ := ext_chain hc ht1 ht i (l - i) (by omega) (fun j hj a b => hS j hj a (by omega))
  rw [show i + (l - i) = l by omega] at h1 h2
  constructor
  · refine h1.trans (mul_le_mul_of_nonneg_right ?_ (ext_pos ht _).le)
    exact (pow_le_pow_right₀ hR1 (by omega)).trans (le_max_left _ _)
  · refine h2.trans (mul_le_mul_of_nonneg_right ?_ (ext_pos ht _).le)
    exact (pow_le_pow_right₀ hi (by omega)).trans (le_max_right _ _)

theorem no_deep_of_cnt_eq {S : Finset (Fin r)} {i l : Fin r} (hil : i ≤ l) (h : cnt S i = cnt S l)
    (j : Fin r) (h1 : i ≤ j) (h2 : j < l) : j ∉ S := by
  intro hj
  unfold cnt at h
  have hsub : S.filter (· < i) ⊂ S.filter (· < l) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j, by simp [hj, h2], by simp [hj, h1]⟩
    · intro x; simp only [Finset.mem_filter]; exact fun ⟨a, b⟩ => ⟨a, lt_of_lt_of_le b hil⟩
  have := Finset.card_lt_card hsub
  omega

theorem no_deep_of_cnt_card {S : Finset (Fin r)} {i : Fin r} (h : cnt S i = S.card) (j : Fin r)
    (h1 : i ≤ j) : j ∉ S := by
  intro hj
  unfold cnt at h
  have hsub : S.filter (· < i) ⊂ S := by
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨j, hj, by simp [hj, h1]⟩
  have := Finset.card_lt_card hsub
  omega

theorem cnt_le_card (S : Finset (Fin r)) (i : Fin r) : cnt S i ≤ S.card := by
  unfold cnt
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

end GlobalTheory.CompanionTheory.CFin.Ratio

namespace GlobalTheory.CompanionTheory.CFin.Ratio

variable {r : ℕ} {c t₁ : ℝ} {t : Fin r → ℝ}

theorem t_pair (hc : 0 < c) (ht1 : 1 ≤ t₁) (ht : t ∈ cone r c) {i l : Fin r}
    (h : cnt (deep t₁ t) i = cnt (deep t₁ t) l) :
    t i ≤ bnd r c t₁ * t l ∧ t l ≤ bnd r c t₁ * t i := by
  rcases le_total i l with hil | hli
  · have := ext_bnd hc ht1 ht (i := i.val) (l := l.val) hil l.isLt.le
      (fun j hj a b => no_deep_of_cnt_eq hil h ⟨j, hj⟩ (show i ≤ (⟨j, hj⟩ : Fin r) from a) b)
    rw [ext_of_lt t i.isLt, ext_of_lt t l.isLt] at this
    exact this
  · have := ext_bnd hc ht1 ht (i := l.val) (l := i.val) hli i.isLt.le
      (fun j hj a b => no_deep_of_cnt_eq hli h.symm ⟨j, hj⟩ (show l ≤ (⟨j, hj⟩ : Fin r) from a) b)
    rw [ext_of_lt t i.isLt, ext_of_lt t l.isLt] at this
    exact ⟨this.2, this.1⟩

theorem t_zero (hc : 0 < c) (ht1 : 1 ≤ t₁) (ht : t ∈ cone r c) {i : Fin r}
    (h : cnt (deep t₁ t) i = (deep t₁ t).card) :
    t i ≤ bnd r c t₁ ∧ 1 ≤ bnd r c t₁ * t i := by
  have := ext_bnd hc ht1 ht (i := i.val) (l := r) i.isLt.le le_rfl
    (fun j hj a _ => no_deep_of_cnt_card h ⟨j, hj⟩ (show i ≤ (⟨j, hj⟩ : Fin r) from a))
  rw [ext_of_lt t i.isLt, ext_of_ge t le_rfl, mul_one] at this
  exact this

theorem wt_pos (ht : t ∈ cone r c) (m : ℕ) (u : Idx r m) : 0 < wt m t u := by
  rcases u with i | k | i
  · exact ht.1 i
  · exact one_pos
  · exact inv_pos.mpr (ht.1 i)

theorem wt_zero (hc : 0 < c) (ht1 : 1 ≤ t₁) (ht : t ∈ cone r c) (m : ℕ) (u : Idx r m)
    (hu : lev m (deep t₁ t) u = 0) :
    (bnd r c t₁)⁻¹ ≤ wt m t u ∧ wt m t u ≤ bnd r c t₁ := by
  have hB := one_le_bnd (r := r) hc ht1
  have hB0 : 0 < bnd r c t₁ := lt_of_lt_of_le one_pos hB
  rcases u with i | k | i
  · simp only [lev] at hu
    obtain ⟨h1, h2⟩ := t_zero hc ht1 ht (i := i) (by linarith)
    show (bnd r c t₁)⁻¹ ≤ t i ∧ t i ≤ bnd r c t₁
    refine ⟨?_, h1⟩
    rw [inv_le_iff_one_le_mul₀' hB0]; exact h2
  · show (bnd r c t₁)⁻¹ ≤ 1 ∧ 1 ≤ bnd r c t₁
    exact ⟨inv_le_one_of_one_le₀ hB, hB⟩
  · simp only [lev] at hu
    obtain ⟨h1, h2⟩ := t_zero hc ht1 ht (i := i) (by linarith)
    have hti := ht.1 i
    show (bnd r c t₁)⁻¹ ≤ (t i)⁻¹ ∧ (t i)⁻¹ ≤ bnd r c t₁
    constructor
    · exact inv_anti₀ hti h1
    · rw [inv_le_iff_one_le_mul₀' hti, mul_comm]; exact h2

end GlobalTheory.CompanionTheory.CFin.Ratio

namespace GlobalTheory.CompanionTheory.CFin.Ratio

theorem ratio_bounded : ∀ (r m : ℕ) (c t₁ : ℝ), 0 < c → 1 ≤ t₁ → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ cone r c,
    ∀ u v : Idx r m, lev m (deep t₁ t) u = lev m (deep t₁ t) v → wt m t u ≤ R * wt m t v := by
  intro r m c t₁ hc ht1
  have hB := one_le_bnd (r := r) hc ht1
  have hB0 : 0 < bnd r c t₁ := lt_of_lt_of_le one_pos hB
  have hBB : bnd r c t₁ ≤ bnd r c t₁ ^ 2 := by nlinarith
  refine ⟨bnd r c t₁ ^ 2, by positivity, ?_⟩
  intro t ht u v huv
  have zero_case : ∀ u v : Idx r m, lev m (deep t₁ t) u = 0 → lev m (deep t₁ t) v = 0 →
      wt m t u ≤ bnd r c t₁ ^ 2 * wt m t v := by
    intro u v hu hv
    have a := (wt_zero hc ht1 ht m u hu).2
    have b := (wt_zero hc ht1 ht m v hv).1
    calc wt m t u ≤ bnd r c t₁ := a
      _ = bnd r c t₁ ^ 2 * (bnd r c t₁)⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left b (by positivity)
  have hcl := cnt_le_card (deep t₁ t)
  rcases u with i | k | i <;> rcases v with l | k' | l
  · simp only [lev] at huv
    have h := (t_pair hc ht1 ht (i := i) (l := l) (by linarith)).1
    show t i ≤ bnd r c t₁ ^ 2 * t l
    exact h.trans (mul_le_mul_of_nonneg_right hBB (ht.1 l).le)
  · exact zero_case _ _ (by simp only [lev] at huv ⊢; linarith) (by simp only [lev])
  · exact zero_case _ _ (by simp only [lev] at huv ⊢; linarith [hcl i, hcl l])
      (by simp only [lev] at huv ⊢; linarith [hcl i, hcl l])
  · exact zero_case _ _ (by simp only [lev]) (by simp only [lev] at huv ⊢; linarith)
  · exact zero_case _ _ (by simp only [lev]) (by simp only [lev])
  · exact zero_case _ _ (by simp only [lev]) (by simp only [lev] at huv ⊢; linarith)
  · exact zero_case _ _ (by simp only [lev] at huv ⊢; linarith [hcl i, hcl l])
      (by simp only [lev] at huv ⊢; linarith [hcl i, hcl l])
  · exact zero_case _ _ (by simp only [lev] at huv ⊢; linarith) (by simp only [lev])
  · simp only [lev] at huv
    have h := (t_pair hc ht1 ht (i := i) (l := l) (by linarith)).2
    have hti := ht.1 i
    have htl := ht.1 l
    show (t i)⁻¹ ≤ bnd r c t₁ ^ 2 * (t l)⁻¹
    calc (t i)⁻¹ = (t i)⁻¹ * t l * (t l)⁻¹ := by field_simp
      _ ≤ (t i)⁻¹ * (bnd r c t₁ * t i) * (t l)⁻¹ := by gcongr
      _ = bnd r c t₁ * (t l)⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hBB (inv_pos.mpr htl).le

end GlobalTheory.CompanionTheory.CFin.Ratio
