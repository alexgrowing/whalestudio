import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SupportSubsetMonoBox

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Scalar

theorem abs_prod_le_pow {α : Type*} (s : Finset α) (y : α → ℝ) {Y : ℝ} (hy : ∀ i ∈ s, |y i| ≤ Y) :
    |∏ i ∈ s, y i| ≤ Y ^ s.card := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |y i| ≤ ∏ _i ∈ s, Y := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hy
    _ = Y ^ s.card := Finset.prod_const Y

theorem card_filter_lt_add_gt {α : Type*} [LinearOrder α] (s : Finset α) {i : α} (hi : i ∈ s) :
    (s.filter (· < i)).card + (s.filter (i < ·)).card ≤ s.card - 1 := by
  rw [← Finset.card_erase_of_mem hi, ← Finset.card_union_of_disjoint
    (Finset.disjoint_filter.mpr fun j _ h1 h2 => lt_asymm h1 h2)]
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_union, Finset.mem_filter] at hj
  rw [Finset.mem_erase]
  rcases hj with ⟨hj, h⟩ | ⟨hj, h⟩
  · exact ⟨ne_of_lt h, hj⟩
  · exact ⟨ne_of_gt h, hj⟩

theorem prod_sub_eq_sum {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) :
    ∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) =
      ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j := by
  have h := Finset.prod_add_ordered s y (fun i => -ε i)
  simp only [← sub_eq_add_neg] at h
  rw [h]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem abs_prod_sub_prod_le {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) {Y E : ℝ}
    (hY : 1 ≤ Y) (hE : 0 ≤ E) (hy : ∀ i ∈ s, |y i| ≤ Y) (hε : ∀ i ∈ s, |ε i| ≤ E) :
    |∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i)| ≤ s.card * E * (Y + E) ^ (s.card - 1) := by
  rw [prod_sub_eq_sum]
  have hYE : 1 ≤ Y + E := by linarith
  calc |∑ i ∈ s, ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j|
      ≤ ∑ i ∈ s, |ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, E * (Y + E) ^ (s.card - 1) := Finset.sum_le_sum fun i hi => ?_
    _ = s.card * E * (Y + E) ^ (s.card - 1) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [abs_mul, abs_mul]
  have h1 : |∏ j ∈ s with j < i, (y j - ε j)| ≤ (Y + E) ^ (s.filter (· < i)).card :=
    abs_prod_le_pow _ _ fun j hj => by
      have hj' := (Finset.mem_filter.mp hj).1
      exact (abs_sub _ _).trans (add_le_add (hy j hj') (hε j hj'))
  have h2 : |∏ j ∈ s with i < j, y j| ≤ (Y + E) ^ (s.filter (i < ·)).card :=
    abs_prod_le_pow _ _ fun j hj => (hy j (Finset.mem_filter.mp hj).1).trans (by linarith)
  have hc := card_filter_lt_add_gt s hi
  calc |ε i| * |∏ j ∈ s with j < i, (y j - ε j)| * |∏ j ∈ s with i < j, y j|
      ≤ E * (Y + E) ^ (s.filter (· < i)).card * (Y + E) ^ (s.filter (i < ·)).card := by
        gcongr
        exact hε i hi
    _ = E * (Y + E) ^ ((s.filter (· < i)).card + (s.filter (i < ·)).card) := by rw [pow_add]; ring
    _ ≤ E * (Y + E) ^ (s.card - 1) := by gcongr <;> first | exact hYE | omega

theorem abs_prod_sub_prod_sub_lin_le {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) {Y E : ℝ}
    (hY : 1 ≤ Y) (hE : 0 ≤ E) (hy : ∀ i ∈ s, |y i| ≤ Y) (hε : ∀ i ∈ s, |ε i| ≤ E) :
    |∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) -
        ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j| ≤
      s.card * ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
  rw [prod_sub_eq_sum, ← Finset.sum_sub_distrib]
  have hYE : 1 ≤ Y + E := by linarith
  calc |∑ i ∈ s, (ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
          ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j)|
      ≤ ∑ i ∈ s, |ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
          ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) :=
        Finset.sum_le_sum fun i hi => ?_
    _ = s.card * ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [show ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
      ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j =
      -(ε i * (∏ j ∈ s with j < i, y j - ∏ j ∈ s with j < i, (y j - ε j)) *
        ∏ j ∈ s with i < j, y j) by ring, abs_neg, abs_mul, abs_mul]
  set a := (s.filter (· < i)).card
  set b := (s.filter (i < ·)).card
  have h1 := abs_prod_sub_prod_le (s.filter (· < i)) y ε hY hE
    (fun j hj => hy j (Finset.mem_filter.mp hj).1) (fun j hj => hε j (Finset.mem_filter.mp hj).1)
  have h2 : |∏ j ∈ s with i < j, y j| ≤ (Y + E) ^ b :=
    abs_prod_le_pow _ _ fun j hj => (hy j (Finset.mem_filter.mp hj).1).trans (by linarith)
  have hc := card_filter_lt_add_gt s hi
  have has : (a : ℝ) ≤ ((s.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right a b).trans hc
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have : (s.filter (· < i)) = ∅ := Finset.card_eq_zero.mp ha
    rw [this, Finset.prod_empty, Finset.prod_empty, sub_self, abs_zero, mul_zero, zero_mul]
    positivity
  calc |ε i| * |∏ j ∈ s with j < i, y j - ∏ j ∈ s with j < i, (y j - ε j)| * |∏ j ∈ s with i < j, y j|
      ≤ E * (a * E * (Y + E) ^ (a - 1)) * (Y + E) ^ b := by
        gcongr
        exact hε i hi
    _ = a * E ^ 2 * (Y + E) ^ (a - 1 + b) := by rw [pow_add]; ring
    _ ≤ ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
        gcongr <;> first | exact hYE | omega | exact has

end Scalar

theorem prod_update_split {n : ℕ} (g : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∏ j, Function.update g i t j = t * (∏ j with j < i, g j) * ∏ j with i < j, g j := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), mul_assoc, ← Finset.prod_union
    (Finset.disjoint_filter.mpr fun j _ h1 h2 => lt_asymm h1 h2)]
  congr 2
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ne_of_lt h
    · exact ne_of_gt h

section Geo

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev uv (k : K) : K → ℤ := Pi.single k 1

def SymmAt (n : ℕ) (V : Ideal (MRing ι)) : Prop :=
  ∀ (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)), geoNum n V (a ∘ σ) = geoNum n V a

theorem geoNum_snoc (n : ℕ) (V : Ideal (MRing ι)) (u : Fin n → K → ℤ) (b : K → ℤ) :
    geoNum (n + 1) V (Fin.snoc u b) = ∑ k, b k * geoNum (n + 1) V (Fin.snoc u (uv k)) := by
  simp only [geoNum, Fin.snoc_last, Fin.init_snoc]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [uv, Pi.single_apply]
  · simp

theorem geoNum_update (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ)
    (i : Fin n) (z : K → ℤ) :
    geoNum n V (Function.update v i z) = ∑ k, z k * geoNum n V (Function.update v i (uv k)) := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set σ := Equiv.swap i (Fin.last m)
    have key : ∀ w : K → ℤ, geoNum (m + 1) V (Function.update v i w) =
        geoNum (m + 1) V (Fin.snoc (Fin.init (v ∘ σ)) w) := by
      intro w
      rw [← hS (Function.update v i w) σ, Function.update_comp_equiv]
      rw [show σ.symm i = Fin.last m by simp [σ]]
      conv_lhs => rw [← Fin.snoc_init_self (v ∘ σ)]
      rw [Fin.update_snoc_last]
    rw [key z, geoNum_snoc]
    simp_rw [key]

def geoML (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) :
    MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ where
  toFun := geoNum n V
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    rw [geoNum_update n V hS m i (x + y), geoNum_update n V hS m i x, geoNum_update n V hS m i y,
      ← Finset.sum_add_distrib]
    simp [add_mul]
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    rw [geoNum_update n V hS m i (c • x), geoNum_update n V hS m i x, smul_eq_mul, Finset.mul_sum]
    simp [mul_assoc]

theorem geoNum_expand (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ) :
    geoNum n V v = ∑ r : Fin n → K, (∏ i, v i (r i)) * geoNum n V (fun i => uv (r i)) := by
  have h1 : v = fun i => ∑ k, v i k • uv k := by
    funext i
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  have := (geoML n V hS).map_sum (fun i k => v i k • uv k)
  conv_lhs => rw [h1]
  change geoML n V hS _ = _
  rw [this]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

def nrm (z : K → ℤ) : ℝ := ∑ k, |(z k : ℝ)|

theorem abs_le_nrm (z : K → ℤ) (k : K) : |(z k : ℝ)| ≤ nrm z :=
  Finset.single_le_sum (f := fun k => |(z k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)

theorem nrm_nonneg (z : K → ℤ) : 0 ≤ nrm z := Finset.sum_nonneg fun _ _ => abs_nonneg _

def coefB (n : ℕ) (V : Ideal (MRing ι)) : ℝ :=
  ∑ r : Fin n → K, |(geoNum n V (fun i => uv (r i)) : ℝ)|

theorem coefB_nonneg (n : ℕ) (V : Ideal (MRing ι)) : 0 ≤ coefB n V :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem geoNum_expand_real (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ) :
    (geoNum n V v : ℝ) =
      ∑ r : Fin n → K, (∏ i, (v i (r i) : ℝ)) * (geoNum n V (fun i => uv (r i)) : ℝ) := by
  rw [geoNum_expand n V hS v]
  push_cast
  rfl

theorem geoNum_shift_est (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (x c : K → ℤ) :
    |(geoNum n V (fun _ => x) : ℝ) - geoNum n V (fun _ => x - c)| ≤
      coefB n V * (n * nrm c * (nrm x + 1 + nrm c) ^ (n - 1)) := by
  rw [geoNum_expand_real n V hS, geoNum_expand_real n V hS, ← Finset.sum_sub_distrib, coefB,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_prod_sub_prod_le (Finset.univ : Finset (Fin n)) (fun i => (x (r i) : ℝ))
    (fun i => (c (r i) : ℝ)) (Y := nrm x + 1) (E := nrm c) (by linarith [nrm_nonneg x]) (nrm_nonneg c)
    (fun i _ => (abs_le_nrm x _).trans (by linarith)) (fun i _ => abs_le_nrm c _)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  simp only [Pi.sub_apply, Int.cast_sub]
  exact this

theorem geoNum_update_eq_snoc (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt (m + 1) V) (x e : K → ℤ)
    (i : Fin (m + 1)) :
    geoNum (m + 1) V (Function.update (fun _ => x) i e) = geoNum (m + 1) V (Fin.snoc (fun _ => x) e) := by
  rw [← hS _ (Equiv.swap i (Fin.last m)), Function.update_comp_equiv]
  rw [show (Equiv.swap i (Fin.last m)).symm i = Fin.last m by simp]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.snoc_castSucc]

theorem geoNum_diff_est (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt (m + 1) V) (x : K → ℤ) (b : K) :
    |(geoNum (m + 1) V (fun _ => x) : ℝ) - geoNum (m + 1) V (fun _ => x - uv b) -
        (m + 1) * geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b))| ≤
      coefB (m + 1) V * ((m + 1) * m * (nrm x + 2) ^ (m + 1 - 2)) := by
  have hlin : ((m + 1 : ℕ) : ℝ) * geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b)) =
      ∑ i : Fin (m + 1), (geoNum (m + 1) V (Function.update (fun _ => x) i (uv b)) : ℝ) := by
    have h : ∀ i : Fin (m + 1), (geoNum (m + 1) V (Function.update (fun _ => x) i (uv b)) : ℝ) =
        geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b)) := fun i => by
      rw [geoNum_update_eq_snoc m V hS x (uv b) i]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  push_cast at hlin
  rw [hlin, geoNum_expand_real (m + 1) V hS (fun _ => x),
    geoNum_expand_real (m + 1) V hS (fun _ => x - uv b),
    Finset.sum_congr rfl fun i _ => geoNum_expand_real (m + 1) V hS (Function.update (fun _ => x) i (uv b))]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, coefB, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← Finset.sum_mul, ← sub_mul, ← sub_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_prod_sub_prod_sub_lin_le (Finset.univ : Finset (Fin (m + 1))) (fun i => (x (r i) : ℝ))
    (fun i => (uv b (r i) : ℝ)) (Y := nrm x + 1) (E := 1) (by linarith [nrm_nonneg x]) zero_le_one
    (fun i _ => (abs_le_nrm x _).trans (by linarith))
    (fun i _ => by simp only [uv, Pi.single_apply]; split_ifs <;> simp)
  simp only [Finset.card_univ, Fintype.card_fin, one_pow, mul_one] at this
  rw [show nrm x + 1 + 1 = nrm x + 2 by ring] at this
  have e1 : (∏ i, (((x - uv b) (r i) : ℤ) : ℝ)) = ∏ i, ((x (r i) : ℝ) - (uv b (r i) : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Pi.sub_apply]
  have e2 : ∀ i, (∏ j, ((Function.update (fun _ => x) i (uv b) j (r j) : ℤ) : ℝ)) =
      (uv b (r i) : ℝ) * (∏ j with j < i, (x (r j) : ℝ)) * ∏ j with i < j, (x (r j) : ℝ) := by
    intro i
    rw [← prod_update_split]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [e1, Finset.sum_congr rfl fun i _ => e2 i]
  push_cast at this
  exact this

end Geo

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
