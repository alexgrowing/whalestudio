import Mathlib

set_option autoImplicit false
noncomputable section
open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.LF.InvFun

variable {σ R : Type} [CommRing R]

theorem pow_sub_pow_order (x y : MvPowerSeries σ R) (k : ℕ∞) (hxy : k ≤ (x - y).order)
    (hx : 1 ≤ x.order) (hy : 1 ≤ y.order) (n : ℕ) :
    k + n ≤ (x ^ n - y ^ n).order + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = (x ^ n - y ^ n) * x + y ^ n * (x - y) := by ring
    have hyn : (n : ℕ∞) ≤ (y ^ n).order := by
      refine le_trans ?_ (le_order_pow (f := y) n)
      simpa using (nsmul_le_nsmul_right hy n)
    have h1 : (x ^ n - y ^ n).order + x.order ≤ ((x ^ n - y ^ n) * x).order := le_order_mul
    have h2 : (y ^ n).order + (x - y).order ≤ (y ^ n * (x - y)).order := le_order_mul
    have hm := min_order_le_add (f := (x ^ n - y ^ n) * x) (g := y ^ n * (x - y))
    rw [e]
    refine le_trans ?_ (add_le_add hm (le_refl (1 : ℕ∞)))
    rw [← min_add_add_right]
    refine le_min ?_ ?_
    · calc k + ((n + 1 : ℕ) : ℕ∞) = (k + n) + 1 := by push_cast; ring
        _ ≤ ((x ^ n - y ^ n).order + 1) + 1 := by gcongr
        _ ≤ ((x ^ n - y ^ n).order + x.order) + 1 := by gcongr
        _ ≤ _ := by gcongr
    · calc k + ((n + 1 : ℕ) : ℕ∞) = ((n : ℕ∞) + k) + 1 := by push_cast; ring
        _ ≤ ((y ^ n).order + (x - y).order) + 1 := by gcongr
        _ ≤ _ := by gcongr

theorem prod_sub_prod_order {ι : Type} (x y : ι → MvPowerSeries σ R) (n : ι → ℕ) (k : ℕ∞)
    (hxy : ∀ i, k ≤ (x i - y i).order) (hx : ∀ i, 1 ≤ (x i).order) (hy : ∀ i, 1 ≤ (y i).order)
    (s : Finset ι) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤ (∏ i ∈ s, x i ^ n i).order ∧
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤ (∏ i ∈ s, y i ^ n i).order ∧
    k + (∑ i ∈ s, n i : ℕ) ≤ (∏ i ∈ s, x i ^ n i - ∏ i ∈ s, y i ^ n i).order + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨hP, hQ, hPQ⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hxa : ((n a : ℕ) : ℕ∞) ≤ (x a ^ n a).order :=
      le_trans (by simpa using nsmul_le_nsmul_right (hx a) (n a)) (le_order_pow _)
    have hya : ((n a : ℕ) : ℕ∞) ≤ (y a ^ n a).order :=
      le_trans (by simpa using nsmul_le_nsmul_right (hy a) (n a)) (le_order_pow _)
    have hda := pow_sub_pow_order (x a) (y a) k (hxy a) (hx a) (hy a) (n a)
    refine ⟨?_, ?_, ?_⟩
    · push_cast at hP ⊢; exact le_trans (add_le_add hxa hP) le_order_mul
    · push_cast at hQ ⊢; exact le_trans (add_le_add hya hQ) le_order_mul
    · have e : x a ^ n a * ∏ i ∈ s, x i ^ n i - y a ^ n a * ∏ i ∈ s, y i ^ n i =
          (x a ^ n a - y a ^ n a) * ∏ i ∈ s, x i ^ n i +
            y a ^ n a * (∏ i ∈ s, x i ^ n i - ∏ i ∈ s, y i ^ n i) := by ring
      rw [e]
      refine le_trans ?_ (add_le_add min_order_le_add (le_refl (1 : ℕ∞)))
      rw [← min_add_add_right]
      refine le_min ?_ ?_
      · calc k + ((n a + ∑ i ∈ s, n i : ℕ) : ℕ∞) = (k + n a) + (∑ i ∈ s, n i : ℕ) := by push_cast; ring
          _ ≤ ((x a ^ n a - y a ^ n a).order + 1) + (∏ i ∈ s, x i ^ n i).order := by gcongr
          _ = ((x a ^ n a - y a ^ n a).order + (∏ i ∈ s, x i ^ n i).order) + 1 := by ring
          _ ≤ _ := by gcongr; exact le_order_mul
      · calc k + ((n a + ∑ i ∈ s, n i : ℕ) : ℕ∞) = (n a : ℕ∞) + (k + (∑ i ∈ s, n i : ℕ)) := by
              push_cast; ring
          _ ≤ (y a ^ n a).order + ((∏ i ∈ s, x i ^ n i - ∏ i ∈ s, y i ^ n i).order + 1) := by gcongr
          _ = ((y a ^ n a).order + (∏ i ∈ s, x i ^ n i - ∏ i ∈ s, y i ^ n i).order) + 1 := by ring
          _ ≤ _ := by gcongr; exact le_order_mul

theorem subst_sub_subst_order [Finite σ] (a b : σ → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (k : ℕ)
    (hab : ∀ i, (k : ℕ∞) ≤ (a i - b i).order) (N : MvPowerSeries σ R) (hN : 2 ≤ N.order) :
    ((k + 1 : ℕ) : ℕ∞) ≤ (subst a N - subst b N).order := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hsb : HasSubst b := hasSubst_of_constantCoeff_zero hb
  apply le_order
  intro e he
  have he' : e.degree < k + 1 := by exact_mod_cast he
  rw [map_sub, coeff_subst hsa, coeff_subst hsb,
    ← finsum_sub_distrib (coeff_subst_finite hsa N e) (coeff_subst_finite hsb N e)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : coeff d N = 0
  · simp [hd]
  rw [← smul_sub, ← map_sub]
  have h2 : (2 : ℕ∞) ≤ (d.degree : ℕ∞) := le_trans hN (order_le hd)
  have h2' : 2 ≤ d.degree := by exact_mod_cast h2
  have hx : ∀ i, 1 ≤ (a i).order := fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha i)
  have hy : ∀ i, 1 ≤ (b i).order := fun i => one_le_order_iff_constCoeff_eq_zero.2 (hb i)
  obtain ⟨-, -, hP⟩ := prod_sub_prod_order a b (fun i => d i) k hab hx hy d.support
  have hdeg : (∑ i ∈ d.support, d i) = d.degree := rfl
  rw [hdeg] at hP
  have hz : coeff e (d.prod (fun s m => a s ^ m) - d.prod (fun s m => b s ^ m)) = 0 := by
    apply coeff_of_lt_order
    change (e.degree : ℕ∞) < (∏ i ∈ d.support, a i ^ d i - ∏ i ∈ d.support, b i ^ d i).order
    by_cases htop : (∏ i ∈ d.support, a i ^ d i - ∏ i ∈ d.support, b i ^ d i).order = ⊤
    · rw [htop]; exact ENat.natCast_lt_top _
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hm] at hP ⊢
      have hP' : k + d.degree ≤ m + 1 := by exact_mod_cast hP
      exact_mod_cast (by omega : e.degree < m)
  rw [hz, smul_zero]

theorem eq_single_of_degree_eq_one {e : σ →₀ ℕ} (h : e.degree = 1) : ∃ j, e = Finsupp.single j 1 := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at h
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : Finsupp.single j 1 ≤ e := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  refine ⟨j, ?_⟩
  have hsum : e = (e - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hle).symm
  have hd : (e - Finsupp.single j 1).degree = 0 := by
    have h2 := congrArg Finsupp.degree hsum
    rw [map_add, Finsupp.degree_single, h] at h2
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hsum, hd, zero_add]

section Inv

variable [Fintype σ] [DecidableEq σ]

def lin (A : Matrix σ σ R) (f : σ → MvPowerSeries σ R) : σ → MvPowerSeries σ R :=
  fun i => ∑ j, C (A i j) * f j

theorem order_lin (A : Matrix σ σ R) (f : σ → MvPowerSeries σ R) (k : ℕ∞) (h : ∀ j, k ≤ (f j).order)
    (i : σ) : k ≤ (lin A f i).order := by
  apply le_order
  intro e he
  rw [lin, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_C_mul, coeff_of_lt_order (lt_of_lt_of_le he (h j)), mul_zero]

theorem lin_sub (A : Matrix σ σ R) (f g : σ → MvPowerSeries σ R) (i : σ) :
    lin A f i - lin A g i = lin A (fun j => f j - g j) i := by
  simp only [lin, ← Finset.sum_sub_distrib, mul_sub]

theorem lin_lin (A B : Matrix σ σ R) (f : σ → MvPowerSeries σ R) :
    lin A (lin B f) = lin (A * B) f := by
  funext i
  simp only [lin, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum, ← mul_assoc, ← map_mul]
  exact Finset.sum_comm

theorem lin_one (f : σ → MvPowerSeries σ R) : lin 1 f = f := by
  funext i
  simp [lin, Matrix.one_apply]

theorem constantCoeff_lin (A : Matrix σ σ R) (f : σ → MvPowerSeries σ R) (h : ∀ j, constantCoeff (f j) = 0)
    (i : σ) : constantCoeff (lin A f i) = 0 := by
  simp [lin, h]

theorem subst_lin (a : σ → MvPowerSeries σ R) (ha : HasSubst a) (A : Matrix σ σ R) (i : σ) :
    subst a (lin A (fun j => X j) i) = lin A a i := by
  rw [lin, ← coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom ha, subst_C, subst_X ha]

def nl (φ : σ → MvPowerSeries σ R) (L : Matrix σ σ R) : σ → MvPowerSeries σ R :=
  fun i => φ i - lin L (fun j => X j) i

theorem two_le_order_nl (φ : σ → MvPowerSeries σ R) (L : Matrix σ σ R)
    (h0 : ∀ i, constantCoeff (φ i) = 0) (h1 : ∀ i j, coeff (Finsupp.single j 1) (φ i) = L i j) (i : σ) :
    2 ≤ (nl φ L i).order := by
  apply le_order
  intro e he
  have he' : e.degree < 2 := by exact_mod_cast he
  rcases (by omega : e.degree = 0 ∨ e.degree = 1) with h | h
  · rw [Finsupp.degree_eq_zero_iff] at h
    subst h
    rw [coeff_zero_eq_constantCoeff_apply, nl, map_sub, h0, constantCoeff_lin _ _ (fun j => constantCoeff_X j)]
    simp
  · obtain ⟨j, rfl⟩ := eq_single_of_degree_eq_one h
    rw [nl, map_sub, h1, lin, map_sum]
    simp only [coeff_C_mul, coeff_X]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hh
      exact hb ((Finsupp.single_left_inj one_ne_zero).mp hh).symm
    · simp

def it (φ : σ → MvPowerSeries σ R) (L M : Matrix σ σ R) : ℕ → σ → MvPowerSeries σ R
  | 0 => 0
  | n + 1 => lin M (fun j => X j - subst (it φ L M n) (nl φ L j))

end Inv

section Inv2

variable [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries σ R) (L M : Matrix σ σ R)
  (hnl : ∀ i, 2 ≤ (nl φ L i).order)

include hnl in
theorem constantCoeff_nl (i : σ) : constantCoeff (nl φ L i) = 0 :=
  one_le_order_iff_constCoeff_eq_zero.1 (le_trans (by norm_num) (hnl i))

include hnl in
theorem constantCoeff_it (n : ℕ) (i : σ) : constantCoeff (it φ L M n i) = 0 := by
  induction n generalizing i with
  | zero => simp [it]
  | succ n ih =>
    have hs : HasSubst (it φ L M n) := hasSubst_of_constantCoeff_zero ih
    rw [it]
    refine constantCoeff_lin _ _ (fun j => ?_) i
    rw [map_sub, constantCoeff_X, constantCoeff_subst_eq_zero hs ih (constantCoeff_nl φ L hnl j), sub_zero]

include hnl in
theorem order_it_step (n : ℕ) (i : σ) : ((n + 1 : ℕ) : ℕ∞) ≤ (it φ L M (n + 1) i - it φ L M n i).order := by
  induction n generalizing i with
  | zero =>
    simp only [it, Pi.zero_apply, sub_zero]
    exact one_le_order_iff_constCoeff_eq_zero.2 (constantCoeff_it φ L M hnl 1 i)
  | succ n ih =>
    rw [show it φ L M (n + 1 + 1) = lin M (fun j => X j - subst (it φ L M (n + 1)) (nl φ L j)) from rfl,
      show it φ L M (n + 1) = lin M (fun j => X j - subst (it φ L M n) (nl φ L j)) from rfl, lin_sub]
    refine order_lin _ _ _ (fun j => ?_) i
    rw [show X j - subst (lin M (fun j => X j - subst (it φ L M n) (nl φ L j))) (nl φ L j) -
        (X j - subst (it φ L M n) (nl φ L j)) =
        subst (it φ L M n) (nl φ L j) - subst (it φ L M (n + 1)) (nl φ L j) by rw [it]; ring]
    refine subst_sub_subst_order _ _ (constantCoeff_it φ L M hnl n) (constantCoeff_it φ L M hnl (n + 1))
      (n + 1) (fun l => ?_) _ (hnl j)
    rw [← neg_sub, order_neg]
    exact ih l

include hnl in
theorem coeff_it_stable (n m : ℕ) (e : σ →₀ ℕ) (he : e.degree ≤ n) (i : σ) :
    coeff e (it φ L M (n + m) i) = coeff e (it φ L M n i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih, ← sub_eq_zero, ← map_sub, ← add_assoc]
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ (order_it_step φ L M hnl (n + m) i)
    exact_mod_cast (by omega : e.degree < n + m + 1)

def lim (i : σ) : MvPowerSeries σ R := fun e => coeff e (it φ L M e.degree i)

theorem coeff_lim (i : σ) (e : σ →₀ ℕ) : coeff e (lim φ L M i) = coeff e (it φ L M e.degree i) := rfl

include hnl in
theorem order_lim_sub (n : ℕ) (i : σ) : ((n + 1 : ℕ) : ℕ∞) ≤ (lim φ L M i - it φ L M n i).order := by
  apply le_order
  intro e he
  have he' : e.degree ≤ n := by
    have : e.degree < n + 1 := by exact_mod_cast he
    omega
  rw [map_sub, coeff_lim, sub_eq_zero, ← Nat.add_sub_cancel' he']
  exact (coeff_it_stable φ L M hnl e.degree (n - e.degree) e le_rfl i).symm

include hnl in
theorem constantCoeff_lim (i : σ) : constantCoeff (lim φ L M i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_lim, map_zero, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_it φ L M hnl]

include hnl in
theorem subst_lim (hLM : L * M = 1) (i : σ) : subst (lim φ L M) (φ i) = X i := by
  have hc := constantCoeff_lim φ L M hnl
  have hs : HasSubst (lim φ L M) := hasSubst_of_constantCoeff_zero hc
  have hφ : φ i = nl φ L i + lin L (fun j => X j) i := by rw [nl, sub_add_cancel]
  have key : ∀ n : ℕ, ((n + 1 : ℕ) : ℕ∞) ≤ (subst (lim φ L M) (φ i) - X i).order := by
    intro n
    have hX : X i = lin L (it φ L M (n + 1)) i + subst (it φ L M n) (nl φ L i) := by
      rw [show it φ L M (n + 1) = lin M (fun j => X j - subst (it φ L M n) (nl φ L j)) from rfl,
        lin_lin, hLM, lin_one, sub_add_cancel]
    have e : subst (lim φ L M) (φ i) - X i =
        (subst (lim φ L M) (nl φ L i) - subst (it φ L M n) (nl φ L i)) +
          lin L (fun j => lim φ L M j - it φ L M (n + 1) j) i := by
      rw [← lin_sub, hφ, subst_add hs, subst_lin _ hs, hX]; ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ (subst_sub_subst_order _ _ hc (constantCoeff_it φ L M hnl n) (n + 1)
        (fun l => order_lim_sub φ L M hnl n l) _ (hnl i))
      exact_mod_cast (by omega : n + 1 ≤ n + 1 + 1)
    · refine order_lin _ _ _ (fun j => le_trans ?_ (order_lim_sub φ L M hnl (n + 1) j)) i
      exact_mod_cast (by omega : n + 1 ≤ n + 1 + 1)
  ext e
  rw [← sub_eq_zero, ← map_sub]
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self e.degree) (key e.degree)

end Inv2

section Main

variable [Fintype σ] [DecidableEq σ]

theorem coeff_lim_single (φ : σ → MvPowerSeries σ R) (L M : Matrix σ σ R) (hnl : ∀ i, 2 ≤ (nl φ L i).order)
    (i j : σ) : coeff (Finsupp.single j 1) (lim φ L M i) = M i j := by
  rw [coeff_lim, Finsupp.degree_single]
  change coeff (Finsupp.single j 1) (lin M (fun l => X l - subst (0 : σ → MvPowerSeries σ R) (nl φ L l)) i) = M i j
  simp only [subst_zero_of_constantCoeff_zero (constantCoeff_nl φ L hnl _), sub_zero]
  rw [lin, map_sum]
  simp only [coeff_C_mul, coeff_X]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg, mul_zero]
    intro hh
    exact hb ((Finsupp.single_left_inj one_ne_zero).mp hh).symm
  · simp

theorem exists_rightInv (φ : σ → MvPowerSeries σ R) (h0 : ∀ i, constantCoeff (φ i) = 0) (L : Matrix σ σ R)
    (h1 : ∀ i j, coeff (Finsupp.single j 1) (φ i) = L i j) (hu : IsUnit L.det) :
    ∃ ψ : σ → MvPowerSeries σ R, (∀ i, constantCoeff (ψ i) = 0) ∧
      (∀ i j, coeff (Finsupp.single j 1) (ψ i) = L⁻¹ i j) ∧ ∀ i, subst ψ (φ i) = X i := by
  have hnl := two_le_order_nl φ L h0 h1
  exact ⟨lim φ L L⁻¹, constantCoeff_lim φ L L⁻¹ hnl, coeff_lim_single φ L L⁻¹ hnl,
    subst_lim φ L L⁻¹ hnl (Matrix.mul_nonsing_inv L hu)⟩

theorem exists_inv (φ : σ → MvPowerSeries σ R) (h0 : ∀ i, constantCoeff (φ i) = 0) (L : Matrix σ σ R)
    (h1 : ∀ i j, coeff (Finsupp.single j 1) (φ i) = L i j) (hu : IsUnit L.det) :
    ∃ ψ : σ → MvPowerSeries σ R, (∀ i, constantCoeff (ψ i) = 0) ∧
      (∀ i, subst ψ (φ i) = X i) ∧ ∀ i, subst φ (ψ i) = X i := by
  obtain ⟨ψ, hψ0, hψ1, hψ⟩ := exists_rightInv φ h0 L h1 hu
  obtain ⟨χ, hχ0, -, hχ⟩ := exists_rightInv ψ hψ0 L⁻¹ hψ1 (Matrix.isUnit_nonsing_inv_det L hu)
  have hsψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hsχ : HasSubst χ := hasSubst_of_constantCoeff_zero hχ0
  have hφχ : φ = χ := by
    funext i
    have h := congrArg (subst χ) (hψ i)
    rw [subst_X hsχ, subst_comp_subst_apply hsψ hsχ] at h
    simp only [hχ] at h
    rw [← h]
    exact (congrFun subst_self (φ i)).symm
  refine ⟨ψ, hψ0, hψ, fun i => ?_⟩
  rw [hφχ]
  exact hχ i

end Main

end ReciprocityTheory.ChartRestriction.G.LF.InvFun
