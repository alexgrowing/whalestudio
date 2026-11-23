import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

namespace PI.QnWCellW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable def cN (r : ℕ) (c : Fin r → ℂ) (j : ℕ) : ℂ := if h : j < r then c ⟨j, h⟩ else 0

@[simp] theorem cN_val (r : ℕ) (c : Fin r → ℂ) (a : Fin r) : cN r c a.val = c a := by
  simp [cN, a.isLt]

theorem cN_mk (r : ℕ) (c : Fin r → ℂ) (j : ℕ) (h : j < r) : c ⟨j, h⟩ = cN r c j := by
  unfold cN
  rw [dif_pos h]

def swp (k r : ℕ) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ p.val ∧ p.val ≤ r + k then p else ⟨2 * r + k - p.val, by omega⟩

theorem swp_val (k r : ℕ) (p : Fin (2 * r + k + 1)) :
    (swp k r p).val = if r ≤ p.val ∧ p.val ≤ r + k then p.val else 2 * r + k - p.val := by
  unfold swp
  split_ifs <;> rfl

theorem swp_swp (k r : ℕ) (p : Fin (2 * r + k + 1)) : swp k r (swp k r p) = p := by
  have hp := p.isLt
  apply Fin.ext
  rw [swp_val, swp_val]
  split_ifs <;> omega

noncomputable def cf (k r : ℕ) (c : Fin r → ℂ) (p : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r then (star (cN r c p.val))⁻¹
  else if p.val ≤ r + k then 1 else cN r c (2 * r + k - p.val)

theorem cf_one (k r : ℕ) (p : Fin (2 * r + k + 1)) : cf k r (fun _ => 1) p = 1 := by
  have hp := p.isLt
  simp only [cf, cN]
  split_ifs <;> first | omega | simp

noncomputable def Wm (k r : ℕ) (S : Finset ℕ) (c : Fin r → ℂ) : Mx k r := fun p q =>
  if q.val < r then
    (if q.val ∈ S then (if p.val = 2 * r + k - q.val then cN r c q.val else 0)
     else if p.val = q.val then 1 else 0)
  else if q.val ≤ r + k then (if p.val = q.val then 1 else 0)
  else if 2 * r + k - q.val ∈ S then
    (if p.val = 2 * r + k - q.val then (star (cN r c (2 * r + k - q.val)))⁻¹ else 0)
  else if p.val = q.val then 1 else 0

theorem eI_ne_esI (k r : ℕ) (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h
  have hl := l.isLt
  rw [Fin.ext_iff] at h
  change l.val = 2 * r + k - l.val at h
  omega

theorem weyl_cell_mul_apply (k r : ℕ) (l : Fin r) (d : ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (w1 k r l d * M) p q =
      if p = esI k r l then d * M (eI k r l) q
      else if p = eI k r l then (star d)⁻¹ * M (esI k r l) q else M p q := by
  have hne := eI_ne_esI k r l
  rw [Matrix.mul_apply]
  by_cases h1 : p = esI k r l
  · subst h1
    rw [if_pos rfl, Finset.sum_eq_single (eI k r l)]
    · simp [w1]
    · intro x _ hx
      simp [w1, hx, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · by_cases h2 : p = eI k r l
    · subst h2
      rw [if_neg h1, if_pos rfl, Finset.sum_eq_single (esI k r l)]
      · simp [w1, hne]
      · intro x _ hx
        simp [w1, hx, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg h1, if_neg h2, Finset.sum_eq_single p]
      · simp [w1, h1, h2]
      · intro x _ hx
        simp [w1, h1, h2, Ne.symm hx]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem Wm_empty (k r : ℕ) (c : Fin r → ℂ) : Wm k r ∅ c = 1 := by
  ext p q
  simp [Wm, Matrix.one_apply, Fin.val_inj]

set_option maxHeartbeats 800000 in

theorem reflection_mul_weyl_cell (k r : ℕ) (S : Finset ℕ) (c : Fin r → ℂ) (a : Fin r) (ha : a.val ∉ S) :
    w1 k r a (c a) * Wm k r S c = Wm k r (insert a.val S) c := by
  ext p q
  rw [weyl_cell_mul_apply]
  have hA := a.isLt
  have hp := p.isLt
  have hq := q.isLt
  have vE : (eI k r a).val = a.val := rfl
  have vS : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [Wm, Finset.mem_insert]
  by_cases h1 : q.val = a.val
  · simp only [h1, ha, eq_self_iff_true, true_or, or_false, if_true, if_false]
    split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | rfl | (exfalso; omega) | (simp; done) | (simp_all; done)
  · by_cases h2 : q.val = 2 * r + k - a.val
    · have e2 : 2 * r + k - (2 * r + k - a.val) = a.val := by omega
      simp only [h2, e2, ha, eq_self_iff_true, true_or, or_false, if_true, if_false]
      split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | rfl | (exfalso; omega) | (simp; done) | (simp_all; done)
    · have h3 : 2 * r + k - q.val ≠ a.val := by omega
      simp only [h1, h3, false_or]
      split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | rfl | (exfalso; omega) | (simp; done) | (simp_all; done)

theorem prod_eq_Wm (k r : ℕ) (c : Fin r → ℂ) : ∀ L : List (Fin r), L.Nodup →
    (L.map fun a => w1 k r a (c a)).prod = Wm k r (L.map Fin.val).toFinset c
  | [], _ => by simpa using (Wm_empty k r c).symm
  | a :: L, h => by
      rw [List.map_cons, List.prod_cons, prod_eq_Wm k r c L (List.nodup_cons.1 h).2, List.map_cons,
        List.toFinset_cons]
      apply reflection_mul_weyl_cell
      intro hm
      simp only [List.mem_toFinset, List.mem_map] at hm
      obtain ⟨b, hb, hba⟩ := hm
      have hba' : b = a := Fin.ext hba
      subst hba'
      exact (List.nodup_cons.1 h).1 hb

theorem wCell_last (k r : ℕ) (c : Fin r → ℂ) : wCell k r (Fin.last r) c = Wm k r (Finset.range r) c := by
  unfold wCell
  rw [List.filter_eq_self.mpr (fun a _ => by simp [a.isLt]), prod_eq_Wm k r c _ (List.nodup_finRange r)]
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and, Finset.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isLt
  · intro hj
    exact ⟨⟨j, hj⟩, rfl⟩

set_option maxHeartbeats 800000 in

theorem Wm_range_apply (k r : ℕ) (c : Fin r → ℂ) (p x : Fin (2 * r + k + 1)) :
    Wm k r (Finset.range r) c p x = if x = swp k r p then cf k r c p else 0 := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [Wm, Finset.mem_range, cf, Fin.ext_iff, swp_val]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega) | (congr 1 <;> congr 1 <;> congr 1 <;> omega) | (simp only [star_one, inv_one, mul_one, one_mul, mul_zero, zero_mul, star_zero, _root_.inv_zero] <;> first | rfl | (congr 1 <;> omega) | (congr 1 <;> congr 1 <;> congr 1 <;> omega))

theorem Wm_mul_apply (k r : ℕ) (c : Fin r → ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Wm k r (Finset.range r) c * M) p q = cf k r c p * M (swp k r p) q := by
  rw [Matrix.mul_apply]
  simp_rw [Wm_range_apply]
  simp [ite_mul]

theorem mul_Wm_apply (k r : ℕ) (c : Fin r → ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (M * Wm k r (Finset.range r) c) p q = M p (swp k r q) * cf k r c (swp k r q) := by
  rw [Matrix.mul_apply]
  have e : ∀ x, Wm k r (Finset.range r) c x q = if x = swp k r q then cf k r c x else 0 := by
    intro x
    rw [Wm_range_apply]
    by_cases h : x = swp k r q
    · subst h
      simp [swp_swp]
    · rw [if_neg h, if_neg]
      intro h'
      apply h
      rw [h', swp_swp]
  simp_rw [e]
  simp [mul_ite]

def μE {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : ℕ) : ℂ :=
  if h : i < k + 1 ∧ j < k + 1 then μ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem μE_mk {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : ℕ) (hi : i < k + 1) (hj : j < k + 1) :
    μ ⟨i, hi⟩ ⟨j, hj⟩ = μE μ i j := by
  unfold μE
  rw [dif_pos ⟨hi, hj⟩]

theorem bigCell_apply (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (p q : Fin (2 * r + k + 1)) :
    bigCell k r c μ p q =
      if q.val < r then (if p.val = 2 * r + k - q.val then cN r c q.val else 0)
      else if q.val ≤ r + k then
        (if r ≤ p.val ∧ p.val ≤ r + k then μE μ (p.val - r) (q.val - r) else 0)
      else (if p.val = 2 * r + k - q.val then (star (cN r c (2 * r + k - q.val)))⁻¹ else 0) := by
  have hq := q.isLt
  simp only [bigCell]
  by_cases h1 : q.val < r
  · rw [dif_pos h1, if_pos h1, cN_mk r c q.val h1]
    have e : (p = esI k r ⟨q.val, h1⟩) ↔ p.val = 2 * r + k - q.val := by
      rw [Fin.ext_iff]
      rfl
    by_cases h : p.val = 2 * r + k - q.val
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (mt e.mp h), if_neg h]
  · rw [dif_neg h1, if_neg h1]
    by_cases h2 : q.val ≤ r + k
    · rw [dif_pos h2, if_pos h2]
      by_cases h3 : r ≤ p.val ∧ p.val ≤ r + k
      · rw [dif_pos h3, if_pos h3]
        exact μE_mk μ _ _ _ _
      · rw [dif_neg h3, if_neg h3]
    · rw [dif_neg h2, if_neg h2]
      have h4 : 2 * r + k - q.val < r := by omega
      rw [cN_mk r c _ h4]

theorem cN_one (r j : ℕ) : cN r (fun _ => 1) j = if j < r then 1 else 0 := by
  unfold cN
  split_ifs <;> rfl

set_option maxHeartbeats 1000000 in
theorem main (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    bigCell k r c μ =
      wCell k r (Fin.last r) c * bigCell k r (fun _ => 1) μ * wCell k r (Fin.last r) (fun _ => 1) := by
  rw [wCell_last, wCell_last]
  ext p q
  rw [mul_Wm_apply, Wm_mul_apply, cf_one, mul_one, bigCell_apply, bigCell_apply]
  have hp := p.isLt
  have hq := q.isLt
  simp only [cf, cN_one, swp_val]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega) | (congr 1 <;> congr 1 <;> congr 1 <;> omega) | (simp only [star_one, inv_one, mul_one, one_mul, mul_zero, zero_mul, star_zero, _root_.inv_zero] <;> first | rfl | (congr 1 <;> omega) | (congr 1 <;> congr 1 <;> congr 1 <;> omega))

end PI.QnWCellW
