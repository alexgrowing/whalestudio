import Mathlib

namespace GlobalTheory.SocleDet

open Matrix

section General

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem det_mul_sub_adjugate_mul_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (i l : n)
    (h : ∀ r, r ≠ i → (M *ᵥ x) r ∈ I) :
    M.det * x l - M.adjugate l i * (M *ᵥ x) i ∈ I := by
  have h1 : (M.adjugate *ᵥ (M *ᵥ x)) l = M.det * x l := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
    simp
  have h2 : (M.adjugate *ᵥ (M *ᵥ x)) l = ∑ r, M.adjugate l r * (M *ᵥ x) r := rfl
  rw [← h1, h2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
  exact I.sum_mem fun r hr => I.mul_mem_left _ (h r (Finset.ne_of_mem_erase hr))

theorem det_mul_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (l : n)
    (h : ∀ r, (M *ᵥ x) r ∈ I) : M.det * x l ∈ I := by
  have := det_mul_sub_adjugate_mul_mem I M x l l fun r _ => h r
  have h2 := I.add_mem this (I.mul_mem_left (M.adjugate l l) (h l))
  simpa using h2

theorem adjugate_updateRow (M : Matrix n n R) (i l : n) (v : n → R) :
    (M.updateRow i v).adjugate l i = M.adjugate l i := by
  rw [adjugate_apply, adjugate_apply, updateRow_idem]

theorem adjugate_cross_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (i j l : n)
    (h : ∀ r, r ≠ i → (M *ᵥ x) r ∈ I) :
    M.adjugate j i * x l - M.adjugate l i * x j ∈ I := by
  have := det_mul_sub_adjugate_mul_mem I (M.updateRow i (Pi.single j 1)) x i l (by
    intro r hr
    have : (M.updateRow i (Pi.single j 1) *ᵥ x) r = (M *ᵥ x) r := by
      simp [mulVec, updateRow_ne hr]
    rw [this]; exact h r hr)
  rw [adjugate_updateRow, ← adjugate_apply] at this
  have e : (M.updateRow i (Pi.single j 1) *ᵥ x) i = x j := by
    simp [mulVec]
  rwa [e] at this

theorem sum_mul_mem_of_syzygy (I : Ideal R) (x C : n → R)
    (hx : ∀ (S : Finset n) (i : n), i ∉ S → ∀ p : R, p * x i ∈ Ideal.span (x '' S) →
      p ∈ Ideal.span (x '' S))
    (hC : ∀ j l, C j * x l - C l * x j ∈ I) (S : Finset n) :
    ∀ s : n → R, ∑ j ∈ S, s j * x j = 0 → ∑ j ∈ S, s j * C j ∈ I := by
  induction S using Finset.induction_on with
  | empty => intro s _; simp
  | insert i S hi ih =>
    intro s hs
    rw [Finset.sum_insert hi] at hs ⊢
    have h1 : s i * x i ∈ Ideal.span (x '' S) := by
      rw [eq_neg_of_add_eq_zero_left hs]
      exact neg_mem (Ideal.sum_mem _ fun j hj =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩))
    obtain ⟨t, ht⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' R).1 (hx S i hi _ h1)
    simp only [smul_eq_mul] at ht
    have h2 := ih (fun j => s j + t j * x i) (by
      rw [← hs, ← ht, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring)
    have h3 : ∑ j ∈ S, t j * (C i * x j - C j * x i) ∈ I :=
      I.sum_mem fun j _ => I.mul_mem_left _ (hC i j)
    have h4 := I.add_mem h2 h3
    convert h4 using 1
    rw [← ht, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem det_sub_det_mem (I : Ideal R) (x : n → R)
    (hx : ∀ (S : Finset n) (i : n), i ∉ S → ∀ p : R, p * x i ∈ Ideal.span (x '' S) →
      p ∈ Ideal.span (x '' S))
    (c c' : Matrix n n R) (h : c *ᵥ x = c' *ᵥ x) (hI : ∀ r, (c *ᵥ x) r ∈ I) :
    c'.det - c.det ∈ I := by
  have key : ∀ S : Finset n, (Matrix.of (fun r j => if r ∈ S then c' r j else c r j)).det - c.det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : Matrix.of (fun r j => if r ∈ (∅ : Finset n) then c' r j else c r j) = c := by
        ext r j; simp
      rw [this]; simp
    | insert i S hi ih =>
      set M : Matrix n n R := Matrix.of (fun r j => if r ∈ S then c' r j else c r j) with hM
      have e1 : Matrix.of (fun r j => if r ∈ insert i S then c' r j else c r j)
          = M.updateRow i (c' i) := by
        ext r j
        by_cases hr : r = i
        · subst hr; simp
        · simp [hM, hr, updateRow_ne hr]
      have e2 : ∀ r, (M *ᵥ x) r = (c *ᵥ x) r := by
        intro r
        by_cases hr : r ∈ S
        · rw [h]
          simp [hM, mulVec, dotProduct, hr]
        · simp [hM, mulVec, dotProduct, hr]
      have h1 := sum_mul_mem_of_syzygy I x (fun j => M.adjugate j i) hx
        (fun j l => adjugate_cross_mem I M x i j l fun r _ => e2 r ▸ hI r) Finset.univ
        (fun j => c' i j - M i j) (by
          have a1 : ∑ j, c' i j * x j = (c *ᵥ x) i := by rw [h]; rfl
          have a2 : ∑ j, M i j * x j = (c *ᵥ x) i := by rw [← e2]; rfl
          simp only [sub_mul, Finset.sum_sub_distrib, a1, a2, sub_self])
      have h2 := I.add_mem h1 ih
      convert h2 using 1
      rw [e1, det_eq_sum_mul_adjugate_row (M.updateRow i (c' i)) i,
        det_eq_sum_mul_adjugate_row M i]
      simp only [adjugate_updateRow, updateRow_self, sub_mul, Finset.sum_sub_distrib]
      ring
  have := key Finset.univ
  have e : Matrix.of (fun r j => if r ∈ (Finset.univ : Finset n) then c' r j else c r j) = c' := by
    ext r j; simp
  rwa [e] at this

end General

section PowerSeries

open MvPowerSeries

variable {k : Type*} [CommRing k] {σ : Type*}

theorem coeff_eq_zero_of_mem_span_pow (N : ℕ) (S : Set σ) (p : MvPowerSeries σ k)
    (hp : p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k) ^ N) '' S))
    (m : σ →₀ ℕ) (hm : ∀ j ∈ S, m j < N) : coeff m p = 0 := by
  classical
  obtain ⟨t, ht, c, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun _).1 hp
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact X_pow_dvd_iff.1 (Dvd.intro_left _ rfl) m (hm j (ht j.2))

theorem mem_span_X_of_coeff (S : Finset σ) : ∀ p : MvPowerSeries σ k,
    (∀ m : σ →₀ ℕ, (∀ j ∈ S, m j = 0) → coeff m p = 0) →
      p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p hp
    have : p = 0 := MvPowerSeries.ext fun m => hp m (by simp)
    simp [this]
  | insert i S hi ih =>
    intro p hp
    let q : MvPowerSeries σ k := fun m => if m i = 0 then coeff m p else 0
    have hq : ∀ m, coeff m q = if m i = 0 then coeff m p else 0 := fun _ => rfl
    have h1 : q ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' (insert i S : Finset σ)) := by
      refine Ideal.span_mono (Set.image_mono (by simp)) (ih q fun m hm => ?_)
      rw [hq]
      split_ifs with h
      · refine hp m fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        exacts [h, hm j hj]
      · rfl
    have h2 : (X i : MvPowerSeries σ k) ∣ p - q :=
      X_dvd_iff.2 fun m hm => by rw [map_sub, hq, if_pos hm, sub_self]
    obtain ⟨r, hr⟩ := h2
    rw [eq_add_of_sub_eq hr]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, by simp, rfl⟩)) h1

theorem mem_span_X_of_mul_X (S : Finset σ) (i : σ) (hi : i ∉ S) (p : MvPowerSeries σ k)
    (hp : p * X i ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S)) :
    p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by
  classical
  refine mem_span_X_of_coeff S p fun m hm => ?_
  have := coeff_eq_zero_of_mem_span_pow 1 S (p * X i) (by simpa using hp)
    (m + Finsupp.single i 1) (fun j hj => by
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      simp [hm j hj, Finsupp.single_eq_of_ne hne])
  rwa [X_def, coeff_add_mul_monomial, mul_one] at this

end PowerSeries

theorem det_notMem_span (k : Type) [Field k] (g N : ℕ) (f : Fin g → MvPowerSeries (Fin g) k)
    (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k))
    (hf : ∀ i, f i = ∑ j, a i j * MvPowerSeries.X j)
    (hN : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range f)) :
    a.det ∉ Ideal.span (Set.range f) := by
  intro hdet
  set x : Fin g → MvPowerSeries (Fin g) k := fun i => MvPowerSeries.X i with hx
  have hN' : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range f) := fun i => by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ (hN i)
  choose b hb using fun i => Ideal.mem_span_range_iff_exists_fun.1 (hN' i)
  set I : Ideal (MvPowerSeries (Fin g) k) := Ideal.span ((fun i => x i ^ (N + 1)) '' Set.univ)
    with hI
  have hxI : ∀ i, x i ^ (N + 1) ∈ I := fun i => Ideal.subset_span ⟨i, trivial, rfl⟩
  let B : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := Matrix.of b
  have hBf : ∀ i, (B *ᵥ f) i = x i ^ (N + 1) := hb
  have haf : a *ᵥ x = f := funext fun i => (hf i).symm
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.1 hdet
  have h1 : (B * a).det ∈ I := by
    rw [det_mul, ← hu, Finset.mul_sum]
    refine I.sum_mem fun j _ => ?_
    rw [mul_left_comm]
    exact I.mul_mem_left _ (det_mul_mem I B f j fun r => hBf r ▸ hxI r)
  have h2 := det_sub_det_mem I x mem_span_X_of_mul_X (B * a) (diagonal fun i => x i ^ N)
    (by
      funext i
      rw [← mulVec_mulVec, haf, hBf, mulVec_diagonal, pow_succ])
    (fun r => by rw [← mulVec_mulVec, haf, hBf]; exact hxI r)
  have h3 : ∏ i, x i ^ N ∈ I := by
    simpa [det_diagonal] using I.add_mem h2 h1
  have h4 : ∏ i, x i ^ N = MvPowerSeries.monomial (∑ i, Finsupp.single i N) (1 : k) := by
    simp only [hx, MvPowerSeries.X_pow_eq]
    rw [MvPowerSeries.prod_monomial]
    simp
  have h5 := coeff_eq_zero_of_mem_span_pow (N + 1) Set.univ _ h3 (∑ i, Finsupp.single i N)
    (fun j _ => by simp [Finsupp.finsetSum_apply, Finsupp.single_apply])
  rw [h4, MvPowerSeries.coeff_monomial_same] at h5
  exact one_ne_zero h5

end GlobalTheory.SocleDet
