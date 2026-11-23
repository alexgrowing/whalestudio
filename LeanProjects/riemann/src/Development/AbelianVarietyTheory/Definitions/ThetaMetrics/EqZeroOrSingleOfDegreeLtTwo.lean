import Mathlib

noncomputable section

namespace GlobalTheory
namespace FormalSeries

open MvPowerSeries

variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]

def jacobian (f : τ → MvPowerSeries σ R) : Matrix τ σ R :=
  Matrix.of fun i j => coeff (Finsupp.single j 1) (f i)

@[simp] theorem jacobian_apply (f : τ → MvPowerSeries σ R) (i : τ) (j : σ) :
    jacobian f i j = coeff (Finsupp.single j 1) (f i) := rfl

@[simp] theorem jacobian_X [DecidableEq σ] :
    jacobian (X : σ → MvPowerSeries σ R) = 1 := by
  ext i j
  rw [jacobian_apply, coeff_index_single_X, Matrix.one_apply]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, Ne.symm h]

theorem le_order_sub {k : ℕ∞} {f g : MvPowerSeries σ R} (hf : k ≤ f.order) (hg : k ≤ g.order) :
    k ≤ (f - g).order := le_order fun d hd => by
  rw [map_sub, coeff_of_lt_order (hd.trans_le hf), coeff_of_lt_order (hd.trans_le hg), sub_zero]

theorem le_order_sum {ι : Type*} {k : ℕ∞} (s : Finset ι) {f : ι → MvPowerSeries σ R}
    (hf : ∀ i ∈ s, k ≤ (f i).order) : k ≤ (∑ i ∈ s, f i).order := le_order fun d hd => by
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => coeff_of_lt_order (hd.trans_le (hf i hi))

theorem coeff_eq_of_le_order_sub {k : ℕ} {f g : MvPowerSeries σ R} (h : (k : ℕ∞) ≤ (f - g).order)
    {d : σ →₀ ℕ} (hd : d.degree < k) : coeff d f = coeff d g := by
  have h' : (d.degree : ℕ∞) < (f - g).order := lt_of_lt_of_le (by exact_mod_cast hd) h
  have := coeff_of_lt_order h'
  rwa [map_sub, sub_eq_zero] at this

theorem eq_of_forall_le_order_sub {f g : MvPowerSeries σ R}
    (h : ∀ k : ℕ, (k : ℕ∞) ≤ (f - g).order) : f = g := by
  ext d
  exact coeff_eq_of_le_order_sub (h (d.degree + 1)) (Nat.lt_succ_self _)

theorem eq_zero_or_single_of_degree_lt_two {d : σ →₀ ℕ} (hd : d.degree < 2) :
    d = 0 ∨ ∃ j, d = Finsupp.single j 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  right
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr h0
  refine ⟨j, ?_⟩
  have hdj : d j ≤ d.degree := Finsupp.le_degree j d
  have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
  ext i
  by_cases hij : i = j
  · rw [hij, Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hij)]
    by_contra hi
    have hsub : ({i, j} : Finset σ) ⊆ d.support := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finsupp.mem_support_iff.mpr hi
      · exact hj
    have hle := Finset.sum_le_sum_of_subset (f := fun x => d x) hsub
    rw [Finset.sum_pair hij, ← Finsupp.degree_apply] at hle
    omega

theorem two_le_order_iff {f : MvPowerSeries σ R} :
    2 ≤ f.order ↔ constantCoeff f = 0 ∧ ∀ j, coeff (Finsupp.single j 1) f = 0 := by
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply]
      refine coeff_of_lt_order ?_
      rw [map_zero, Nat.cast_zero]
      exact lt_of_lt_of_le (by norm_num) h
    · refine coeff_of_lt_order ?_
      rw [Finsupp.degree_single, Nat.cast_one]
      exact lt_of_lt_of_le (by norm_num) h
  · rintro ⟨h0, h1⟩
    have : ((2 : ℕ) : ℕ∞) ≤ f.order := nat_le_order fun d hd => by
      rcases eq_zero_or_single_of_degree_lt_two hd with rfl | ⟨j, rfl⟩
      · rw [coeff_zero_eq_constantCoeff_apply]
        exact h0
      · exact h1 j
    exact_mod_cast this

theorem two_le_order_sub_linear [Fintype σ] {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    2 ≤ (f - ∑ j, coeff (Finsupp.single j 1) f • X j).order := by
  classical
  refine two_le_order_iff.mpr ⟨?_, fun k => ?_⟩
  · simp [map_sub, map_sum, hf]
  · simp [map_sub, map_sum, coeff_index_single_X]

private def Close (k n : ℕ) (P Q : MvPowerSeries τ S) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((k + n : ℕ) : ℕ∞) ≤ (P - Q).order + 1

private theorem Close.one (k : ℕ) : Close k 0 (1 : MvPowerSeries τ S) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  simp

private theorem Close.mul {k n m : ℕ} {P Q P' Q' : MvPowerSeries τ S} (h : Close k n P Q)
    (h' : Close k m P' Q') : Close k (n + m) (P * P') (Q * Q') := by
  obtain ⟨hP, hQ, hPQ⟩ := h
  obtain ⟨hP', hQ', hPQ'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    exact (add_le_add hP hP').trans le_order_mul
  · push_cast
    exact (add_le_add hQ hQ').trans le_order_mul
  · have e : P * P' - Q * Q' = (P - Q) * P' + Q * (P' - Q') := by ring
    rw [e]
    have h1 : ((k + (n + m) : ℕ) : ℕ∞) ≤ ((P - Q) * P').order + 1 :=
      calc ((k + (n + m) : ℕ) : ℕ∞) = ((k + n : ℕ) : ℕ∞) + m := by push_cast; ring
        _ ≤ ((P - Q).order + 1) + P'.order := add_le_add hPQ hP'
        _ = ((P - Q).order + P'.order) + 1 := by ring
        _ ≤ ((P - Q) * P').order + 1 := by gcongr; exact le_order_mul
    have h2 : ((k + (n + m) : ℕ) : ℕ∞) ≤ (Q * (P' - Q')).order + 1 :=
      calc ((k + (n + m) : ℕ) : ℕ∞) = n + ((k + m : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ Q.order + ((P' - Q').order + 1) := add_le_add hQ hPQ'
        _ = (Q.order + (P' - Q').order) + 1 := by ring
        _ ≤ (Q * (P' - Q')).order + 1 := by gcongr; exact le_order_mul
    calc ((k + (n + m) : ℕ) : ℕ∞)
        ≤ min (((P - Q) * P').order + 1) ((Q * (P' - Q')).order + 1) := le_min h1 h2
      _ = min ((P - Q) * P').order (Q * (P' - Q')).order + 1 := min_add_add_right _ _ _
      _ ≤ ((P - Q) * P' + Q * (P' - Q')).order + 1 := by gcongr; exact min_order_le_add

private theorem close_pow_of_close_one {k e : ℕ} {x y : MvPowerSeries τ S} (h : Close k 1 x y) :
    Close k e (x ^ e) (y ^ e) := by
  induction e with
  | zero => simpa using Close.one (τ := τ) (S := S) k
  | succ e ih =>
    rw [pow_succ, pow_succ]
    exact Close.mul ih h

private theorem Close.prod {k : ℕ} {a b : σ → MvPowerSeries τ S}
    (h : ∀ s, Close k 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Close k d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction with
  | zero => simpa using Close.one (τ := τ) (S := S) k
  | single_add i e d _ _ ih =>
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), map_add,
      Finsupp.degree_single]
    exact Close.mul (close_pow_of_close_one (h i)) ih

variable [Algebra R S]

private theorem natCast_lt_of_le_add_one_of_add_two_le {x : ℕ∞} {n m : ℕ} (h : (n : ℕ∞) ≤ x + 1)
    (hm : m + 2 ≤ n) : (m : ℕ∞) < x := by
  induction x using ENat.recTopCoe with
  | top => exact ENat.natCast_lt_top m
  | coe x =>
    have h' : n ≤ x + 1 := by exact_mod_cast h
    exact_mod_cast (by omega : m < x)

theorem le_order_subst_sub_subst [Finite σ] {a b : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) {k : ℕ}
    (hab : ∀ s, (k : ℕ∞) ≤ (a s - b s).order) {h : MvPowerSeries σ R} (hh : 2 ≤ h.order) :
    ((k + 1 : ℕ) : ℕ∞) ≤ (h.subst a - h.subst b).order := by
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hb' : HasSubst b := hasSubst_of_constantCoeff_zero hb
  have hc : ∀ s, Close k 1 (a s) (b s) := fun s =>
    ⟨by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (ha s),
      by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (hb s),
      by push_cast; exact add_le_add (hab s) le_rfl⟩
  refine nat_le_order fun e he => ?_
  rw [map_sub, coeff_subst ha', coeff_subst hb',
    ← finsum_sub_distrib (coeff_subst_finite ha' h e) (coeff_subst_finite hb' h e)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rw [← smul_sub, ← map_sub]
  by_cases hd : coeff d h = 0
  · rw [hd, zero_smul]
  · have h2 : 2 ≤ d.degree := by
      have := hh.trans (order_le hd)
      exact_mod_cast this
    obtain ⟨-, -, hcl⟩ := Close.prod hc d
    rw [coeff_of_lt_order (natCast_lt_of_le_add_one_of_add_two_le hcl (by omega)), smul_zero]

theorem subst_eq_linear_add [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    f.subst a = ∑ j, coeff (Finsupp.single j 1) f • a j +
      (f - ∑ j, coeff (Finsupp.single j 1) f • X j).subst a := by
  rw [← substAlgHom_apply ha, ← substAlgHom_apply ha, map_sub, map_sum]
  simp only [map_smul, substAlgHom_X]
  abel

private theorem coeff_single_subst_eq_zero_of_linear_coeff_zero [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff (a s) = 0) {g : MvPowerSeries σ R}
    (hg : ∀ j, coeff (Finsupp.single j 1) g = 0) (k : τ) :
    coeff (Finsupp.single k 1) (g.subst a) = 0 := by
  classical
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hc : ∀ s, Close 0 1 (a s) (a s) := fun s =>
    ⟨by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (ha s),
      by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (ha s), by simp⟩
  rw [coeff_subst ha']
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : coeff d g = 0
  · rw [hd, zero_smul]
  · by_cases h2 : d.degree < 2
    · rcases eq_zero_or_single_of_degree_lt_two h2 with rfl | ⟨j, rfl⟩
      · rw [Finsupp.prod_zero_index, coeff_one, if_neg (by simp), smul_zero]
      · exact absurd (hg j) hd
    · obtain ⟨hcl, -, -⟩ := Close.prod hc d
      have hlt : ((Finsupp.single k 1 : τ →₀ ℕ).degree : ℕ∞) < (d.prod fun s e => a s ^ e).order := by
        rw [Finsupp.degree_single]
        exact lt_of_lt_of_le (by exact_mod_cast (by omega : 1 < d.degree)) hcl
      rw [coeff_of_lt_order hlt, smul_zero]

theorem coeff_single_subst [Fintype σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (k : τ) :
    coeff (Finsupp.single k 1) (f.subst a) =
      ∑ j, coeff (Finsupp.single j 1) f • coeff (Finsupp.single k 1) (a j) := by
  classical
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [subst_eq_linear_add ha' f, map_add, coeff_single_subst_eq_zero_of_linear_coeff_zero ha, add_zero, map_sum]
  · rfl
  · intro j
    simp [map_sub, map_sum, coeff_index_single_X]

theorem jacobian_subst [Fintype τ] {f : τ → MvPowerSeries σ R}
    (hf : ∀ s, constantCoeff (f s) = 0) (g : υ → MvPowerSeries τ R) :
    jacobian (fun i => (g i).subst f) = jacobian g * jacobian f := by
  ext i k
  simp only [Matrix.mul_apply, jacobian_apply, coeff_single_subst hf, smul_eq_mul]

theorem existsUnique_fixedPoint (Φ : (σ → MvPowerSeries τ S) → (σ → MvPowerSeries τ S))
    (h0 : ∀ a, (∀ s, constantCoeff (a s) = 0) → ∀ s, constantCoeff (Φ a s) = 0)
    (hΦ : ∀ a b (k : ℕ), (∀ s, constantCoeff (a s) = 0) → (∀ s, constantCoeff (b s) = 0) →
      (∀ s, (k : ℕ∞) ≤ (a s - b s).order) → ∀ s, ((k + 1 : ℕ) : ℕ∞) ≤ (Φ a s - Φ b s).order) :
    ∃! a, (∀ s, constantCoeff (a s) = 0) ∧ Φ a = a := by
  have hA0 : ∀ n s, constantCoeff ((Φ^[n] 0) s) = 0 := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih => intro s; rw [Function.iterate_succ_apply']; exact h0 _ ih s
  have hcl : ∀ n j : ℕ, ∀ s, (n : ℕ∞) ≤ ((Φ^[n + j] 0) s - (Φ^[n] 0) s).order := by
    intro n
    induction n with
    | zero => intro j s; simp
    | succ n ih =>
      intro j s
      rw [show n + 1 + j = (n + j) + 1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      exact hΦ _ _ n (hA0 _) (hA0 _) (ih j) s
  have hst : ∀ (d : τ →₀ ℕ) s n, d.degree < n →
      coeff d ((Φ^[n] 0) s) = coeff d ((Φ^[d.degree + 1] 0) s) := by
    intro d s n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show d.degree + 1 ≤ n by omega)
    exact coeff_eq_of_le_order_sub (hcl _ j s) (Nat.lt_succ_self _)
  obtain ⟨a, hca⟩ : ∃ a : σ → MvPowerSeries τ S,
      ∀ s d, coeff d (a s) = coeff d ((Φ^[d.degree + 1] 0) s) :=
    ⟨fun s d => coeff d ((Φ^[d.degree + 1] 0) s), fun s d => rfl⟩
  have hac : ∀ n : ℕ, ∀ s, (n : ℕ∞) ≤ (a s - (Φ^[n] 0) s).order := fun n s =>
    nat_le_order fun d hd => by rw [map_sub, hca, hst d s n hd, sub_self]
  have haz : ∀ s, constantCoeff (a s) = 0 := fun s => by
    rw [← coeff_zero_eq_constantCoeff_apply, hca, coeff_zero_eq_constantCoeff_apply]
    exact hA0 _ s
  have hfix : Φ a = a := by
    funext s
    refine eq_of_forall_le_order_sub fun n => ?_
    have e : Φ a s - a s = (Φ a s - Φ (Φ^[n] 0) s) - (a s - (Φ^[n + 1] 0) s) := by
      rw [Function.iterate_succ_apply']
      abel
    have hn : (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ n
    rw [e]
    exact le_order_sub (hn.trans (hΦ a _ n haz (hA0 n) (hac n) s)) (hn.trans (hac (n + 1) s))
  refine ⟨a, ⟨haz, hfix⟩, ?_⟩
  rintro b ⟨hbz, hbfix⟩
  have key : ∀ n : ℕ, ∀ s, (n : ℕ∞) ≤ (b s - a s).order := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      have := hΦ b a n hbz haz ih s
      rwa [hbfix, hfix] at this
  funext s
  exact eq_of_forall_le_order_sub fun n => key n s

theorem exists_subst_eq [Fintype σ] [Fintype τ] [DecidableEq τ] {u : τ → MvPowerSeries σ R}
    (hu : ∀ i, constantCoeff (u i) = 0) {B : Matrix σ τ R} (hB : jacobian u * B = 1)
    {c : τ → MvPowerSeries υ R} (hc : ∀ i, constantCoeff (c i) = 0) :
    ∃ v : σ → MvPowerSeries υ R, (∀ j, constantCoeff (v j) = 0) ∧ ∀ i, (u i).subst v = c i := by
  obtain ⟨N, hN⟩ : ∃ N : τ → MvPowerSeries σ R,
      ∀ i, N i = u i - ∑ j, coeff (Finsupp.single j 1) (u i) • X j := ⟨_, fun _ => rfl⟩
  have hN2 : ∀ i, 2 ≤ (N i).order := fun i => by rw [hN]; exact two_le_order_sub_linear (hu i)
  have hNc : ∀ i, constantCoeff (N i) = 0 := fun i =>
    one_le_order_iff_constCoeff_eq_zero.mp (le_trans (by norm_num) (hN2 i))
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (σ → MvPowerSeries υ R) → (σ → MvPowerSeries υ R),
      ∀ v j, Φ v j = ∑ i, B j i • (c i - (N i).subst v) := ⟨fun v j => ∑ i, B j i • (c i - (N i).subst v), fun _ _ => rfl⟩
  have h0 : ∀ v, (∀ s, constantCoeff (v s) = 0) → ∀ s, constantCoeff (Φ v s) = 0 := by
    intro v hv j
    rw [hΦ, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [constantCoeff_smul, map_sub, hc i,
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hv) hv (hNc i), sub_zero,
      smul_zero]
  have hΦk : ∀ v w (k : ℕ), (∀ s, constantCoeff (v s) = 0) → (∀ s, constantCoeff (w s) = 0) →
      (∀ s, (k : ℕ∞) ≤ (v s - w s).order) →
        ∀ s, ((k + 1 : ℕ) : ℕ∞) ≤ (Φ v s - Φ w s).order := by
    intro v w k hv hw hvw j
    rw [hΦ, hΦ, ← Finset.sum_sub_distrib]
    refine le_order_sum _ fun i _ => ?_
    rw [← smul_sub, sub_sub_sub_cancel_left]
    have hwv : ∀ s, (k : ℕ∞) ≤ (w s - v s).order := fun s => by
      rw [← neg_sub, order_neg]
      exact hvw s
    exact (le_order_subst_sub_subst hw hv hwv (hN2 i)).trans le_order_smul
  obtain ⟨v, ⟨hv0, hvfix⟩, -⟩ := existsUnique_fixedPoint Φ h0 hΦk
  refine ⟨v, hv0, fun i => ?_⟩
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hvj : ∀ j, v j = ∑ i', B j i' • (c i' - (N i').subst v) := fun j => by
    rw [← hΦ, hvfix]
  rw [subst_eq_linear_add hvs (u i), ← hN i]
  have hlin : ∑ j, coeff (Finsupp.single j 1) (u i) • v j = c i - (N i).subst v :=
    calc ∑ j, coeff (Finsupp.single j 1) (u i) • v j
        = ∑ j, ∑ i', (jacobian u i j * B j i') • (c i' - (N i').subst v) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hvj j, Finset.smul_sum]
          simp only [smul_smul, jacobian_apply]
      _ = ∑ i', (jacobian u * B) i i' • (c i' - (N i').subst v) := by
          rw [Finset.sum_comm]
          simp only [Matrix.mul_apply, Finset.sum_smul]
      _ = c i - (N i).subst v := by
          rw [hB]
          simp [Matrix.one_apply]
  rw [hlin, sub_add_cancel]

theorem exists_subst_inverse [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    {u : τ → MvPowerSeries σ R} (hu : ∀ i, constantCoeff (u i) = 0) {B : Matrix σ τ R}
    (hB : jacobian u * B = 1) (hB' : B * jacobian u = 1) :
    ∃ v : σ → MvPowerSeries τ R, (∀ j, constantCoeff (v j) = 0) ∧
      (∀ i, (u i).subst v = X i) ∧ ∀ j, (v j).subst u = X j := by
  obtain ⟨v, hv0, hv⟩ := exists_subst_eq hu hB (c := (X : τ → MvPowerSeries τ R))
    (fun i => constantCoeff_X i)
  have hJ : jacobian u * jacobian v = 1 := by
    rw [← jacobian_subst hv0 u]
    simp only [hv]
    exact jacobian_X
  have hJv : jacobian v = B :=
    calc jacobian v = (B * jacobian u) * jacobian v := by rw [hB', Matrix.one_mul]
      _ = B := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  obtain ⟨w, hw0, hw⟩ := exists_subst_eq hv0 (B := jacobian u) (by rw [hJv]; exact hB')
    (c := (X : σ → MvPowerSeries σ R)) (fun j => constantCoeff_X j)
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hws : HasSubst w := hasSubst_of_constantCoeff_zero hw0
  have huw : u = w := by
    funext i
    calc u i = (u i).subst (X : σ → MvPowerSeries σ R) := by rw [subst_self]; rfl
      _ = (u i).subst (fun s => (v s).subst w) := by simp only [hw]
      _ = ((u i).subst v).subst w := (subst_comp_subst_apply hvs hws _).symm
      _ = w i := by rw [hv, subst_X hws]
  refine ⟨v, hv0, hv, fun j => ?_⟩
  rw [huw]
  exact hw j

end FormalSeries
end GlobalTheory
