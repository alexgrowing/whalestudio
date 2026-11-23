import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Polynomial

private theorem prod_X_sub_C_dvd_of_eval_eq_zero_of_injOn {O : Type*} [CommRing O] [IsDomain O] (c : ℤ → O) :
    ∀ (s : Finset ℤ), Set.InjOn c (↑s : Set ℤ) → ∀ Q : O[X], (∀ k ∈ s, Q.eval (c k) = 0) →
      (∏ k ∈ s, (X - C (c k))) ∣ Q := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ Q _; simp
  | @insert a s ha ih =>
    intro hinj Q hQ
    have hroot : Q.IsRoot (c a) := hQ a (Finset.mem_insert_self a s)
    obtain ⟨Q', hQ'⟩ : (X - C (c a)) ∣ Q := by
      first
        | exact Polynomial.dvd_iff_isRoot.mpr hroot
        | exact ⟨_, (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot).symm⟩
    have hinj' : Set.InjOn c (↑s : Set ℤ) :=
      hinj.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))
    have hQ'0 : ∀ k ∈ s, Q'.eval (c k) = 0 := by
      intro k hk
      have h1 : Q.eval (c k) = 0 := hQ k (Finset.mem_insert_of_mem hk)
      rw [hQ', eval_mul, eval_sub, eval_X, eval_C] at h1
      have hne : c k - c a ≠ 0 := by
        intro h
        have hka : k = a := hinj (by simp [hk]) (by simp) (sub_eq_zero.mp h)
        exact ha (hka ▸ hk)
      exact (mul_eq_zero.mp h1).resolve_left hne
    rw [Finset.prod_insert ha, hQ']
    exact mul_dvd_mul_left _ (ih hinj' Q' hQ'0)

theorem smul_eq_zero_of_aeval_prod {O : Type*} [CommRing O] [IsDomain O] {V : Type*} [AddCommGroup V] [Module O V]
    (T : Module.End O V) (S₁ S₂ : Finset ℤ) (c : ℤ → O) (d : O) (x : V)
    (hdisj : Disjoint S₁ S₂) (hinj : Set.InjOn c (↑(S₁ ∪ S₂) : Set ℤ))
    (h₁ : aeval T (∏ m ∈ S₁, (X - C (c m))) x = 0)
    (h₂ : aeval T (∏ m ∈ S₂, (X - C (c m))) x = 0)
    (hd : ∀ m ∈ S₁, ((∏ m' ∈ S₁.erase m, (c m - c m')) * ∏ m' ∈ S₂, (c m - c m')) ∣ d) :
    d • x = 0 := by
  have hd' : ∀ m ∈ S₁, ∃ e : O,
      d = ((∏ m' ∈ S₁.erase m, (c m - c m')) * ∏ m' ∈ S₂, (c m - c m')) * e :=
    fun m hm => hd m hm
  choose! e he using hd'
  obtain ⟨R, hR⟩ : ∃ R : O[X], R = (∑ m ∈ S₁, C (e m) * ∏ m' ∈ S₁.erase m, (X - C (c m'))) *
      ∏ m' ∈ S₂, (X - C (c m')) := ⟨_, rfl⟩
  have hRx : aeval T R x = 0 := by
    rw [hR, map_mul]
    first
      | (rw [Module.End.mul_apply, h₂, map_zero])
      | (rw [LinearMap.mul_apply, h₂, map_zero])
      | (simp [h₂])
  have hev : ∀ k ∈ S₁, R.eval (c k) = d := by
    intro k hk
    rw [hR, eval_mul, eval_finset_sum, eval_prod]
    rw [Finset.sum_eq_single k]
    · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      rw [he k hk]
      ring
    · intro m _ hmk
      simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      exact mul_eq_zero_of_right _
        (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hmk, hk⟩) (sub_self _))
    · intro h
      exact absurd hk h
  have hdvd : (∏ m ∈ S₁, (X - C (c m))) ∣ R - C d := by
    apply prod_X_sub_C_dvd_of_eval_eq_zero_of_injOn c S₁
      (hinj.mono (Finset.coe_subset.mpr (by intro y hy; exact Finset.mem_union_left _ hy)))
    intro k hk
    rw [eval_sub, eval_C, hev k hk, sub_self]
  obtain ⟨F, hF⟩ := hdvd
  have hCd : C d = R - (∏ m ∈ S₁, (X - C (c m))) * F := by
    rw [← hF]
    ring
  have hCx : aeval T (C d) x = d • x := by
    first
      | (rw [aeval_C, Module.algebraMap_end_apply])
      | (simp [Algebra.algebraMap_eq_smul_one])
      | simp
  have hP1F : aeval T ((∏ m ∈ S₁, (X - C (c m))) * F) x = 0 := by
    rw [mul_comm, map_mul]
    first
      | (rw [Module.End.mul_apply, h₁, map_zero])
      | (rw [LinearMap.mul_apply, h₁, map_zero])
      | (simp [h₁])
  rw [← hCx, hCd, map_sub, LinearMap.sub_apply, hRx, hP1F, sub_zero]

private theorem emod_add_mul_ediv_eq (a b : ℤ) : a % b + b * (a / b) = a := by
  first
    | exact Int.emod_add_ediv a b
    | (have h := Int.ediv_add_emod a b; linarith)
    | (rw [Int.emod_def]; ring)
    | (have h := Int.emod_def a b; linarith)

private theorem card_filter_dvd_sub_mul_le_Icc_length_add (q : ℤ) (hq : 0 < q) (lo hi r : ℤ) (hlh : lo ≤ hi) :
    (((Finset.Icc lo hi).filter (fun x => q ∣ r - x)).card : ℤ) * q ≤ hi - lo + q := by
  obtain ⟨s, hs⟩ : ∃ s : Finset ℤ, s = (Finset.Icc lo hi).filter (fun x => q ∣ r - x) := ⟨_, rfl⟩
  rw [← hs]
  have hmaps : ∀ x ∈ s, (x - lo) / q ∈ Finset.Icc (0 : ℤ) ((hi - lo) / q) := by
    intro x hx
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hx
    rw [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by linarith [hx.1.1]) hq.le, Int.ediv_le_ediv hq (by linarith [hx.1.2])⟩
  have hinj : Set.InjOn (fun x : ℤ => (x - lo) / q) (↑s : Set ℤ) := by
    intro x hx y hy hxy
    have hx' : x ∈ s := hx
    have hy' : y ∈ s := hy
    rw [hs, Finset.mem_filter] at hx' hy'
    obtain ⟨u, hu⟩ := hx'.2
    obtain ⟨v, hv⟩ := hy'.2
    have hxy' : (x - lo) / q = (y - lo) / q := hxy
    have e1 := emod_add_mul_ediv_eq (x - lo) q
    have e2 := emod_add_mul_ediv_eq (y - lo) q
    have n1 := Int.emod_nonneg (x - lo) (ne_of_gt hq)
    have n2 := Int.emod_nonneg (y - lo) (ne_of_gt hq)
    have l1 := Int.emod_lt_of_pos (x - lo) hq
    have l2 := Int.emod_lt_of_pos (y - lo) hq
    rw [hxy'] at e1
    have hw : q * (v - u) = (x - lo) % q - (y - lo) % q := by
      linear_combination hu - hv - e1 + e2
    have hlt : q * (v - u) < q := by linarith
    have hgt : -q < q * (v - u) := by linarith
    have h1' : v - u < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h2' : -1 < v - u := by
      by_contra hc
      push_neg at hc
      nlinarith
    have hvu : v = u := by omega
    subst hvu
    linarith
  have hcard : s.card ≤ (Finset.Icc (0 : ℤ) ((hi - lo) / q)).card :=
    Finset.card_le_card_of_injOn (fun x : ℤ => (x - lo) / q) (by intro x hx; exact hmaps x hx) hinj
  rw [Int.card_Icc] at hcard
  have hdiv := emod_add_mul_ediv_eq (hi - lo) q
  have hnn := Int.emod_nonneg (hi - lo) (ne_of_gt hq)
  have hd0 : 0 ≤ (hi - lo) / q := Int.ediv_nonneg (by linarith) hq.le
  generalize (hi - lo) / q = w at hcard hdiv hd0
  have hc : (s.card : ℤ) ≤ w + 1 := by omega
  nlinarith [mul_le_mul_of_nonneg_right hc hq.le]

private theorem padicValInt_eq_card_filter_pow_dvd (l : ℕ) [hl : Fact l.Prime] (N : ℕ) (t : ℤ) (ht : t ≠ 0)
    (htN : t.natAbs ≤ N) :
    padicValInt l t = ((Finset.range (Nat.log l N)).filter (fun k => (l : ℤ) ^ (k + 1) ∣ t)).card := by
  show padicValNat l t.natAbs = _
  have hn : t.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht
  have hdiv : ∀ k : ℕ, ((l : ℤ) ^ k ∣ t ↔ k ≤ padicValNat l t.natAbs) := by
    intro k
    rw [← Nat.cast_pow, ← padicValNat_dvd_iff_le hn]
    first
      | exact Int.natCast_dvd
      | exact Int.ofNat_dvd_left
      | exact Int.coe_nat_dvd_left
  have hle : padicValNat l t.natAbs ≤ Nat.log l N := by
    have h1 : l ^ padicValNat l t.natAbs ∣ t.natAbs := pow_padicValNat_dvd
    have h2 : l ^ padicValNat l t.natAbs ≤ N := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1) htN
    first
      | exact Nat.le_log_of_pow_le hl.out.one_lt h2
      | exact (Nat.pow_le_iff_le_log hl.out.one_lt (by omega)).1 h2
  have hfilt : (Finset.range (Nat.log l N)).filter (fun k => (l : ℤ) ^ (k + 1) ∣ t) =
      Finset.range (padicValNat l t.natAbs) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, hdiv]
    omega
  rw [hfilt, Finset.card_range]

private theorem sum_padicValInt_sub_eq_sum_card_filter_pow_dvd (l : ℕ) [Fact l.Prime] (N : ℕ) (m : ℤ) (T : Finset ℤ)
    (hT : ∀ t ∈ T, t ≠ m ∧ (m - t).natAbs ≤ N) :
    ∑ t ∈ T, padicValInt l (m - t) =
      ∑ k ∈ Finset.range (Nat.log l N), (T.filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).card := by
  have h : ∀ t ∈ T, padicValInt l (m - t) =
      ((Finset.range (Nat.log l N)).filter (fun k => (l : ℤ) ^ (k + 1) ∣ m - t)).card :=
    fun t ht => padicValInt_eq_card_filter_pow_dvd l N (m - t) (sub_ne_zero.mpr (hT t ht).1.symm) (hT t ht).2
  rw [Finset.sum_congr rfl h]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

private theorem geom_sum_inv_pow_succ_le_inv_sub_one (l : ℝ) (hl : 2 ≤ l) (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / l ^ (k + 1)) ≤ 1 / (l - 1) := by
  have hl0 : l ≠ 0 := ne_of_gt (by linarith)
  have key : ∀ n : ℕ, (l - 1) * ∑ k ∈ Finset.range n, (1 / l ^ (k + 1)) = 1 - 1 / l ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      first
        | (field_simp; ring)
        | field_simp
        | (rw [pow_succ]; field_simp; ring)
  have hpos : 0 < l - 1 := by linarith
  have h1 := key K
  have h2 : 0 < 1 / l ^ K := one_div_pos.mpr (pow_pos (by linarith) K)
  first
    | (rw [le_div_iff₀ hpos]; linarith)
    | (rw [le_div_iff hpos]; linarith)

private theorem sum_card_le_div_sub_one_add_mul_of_mul_pow_le (l : ℕ) (hl : 2 ≤ l) (K : ℕ) (w : ℝ) (hw : 0 ≤ w) (δ : ℝ) (f : ℕ → ℕ)
    (hf : ∀ k ∈ Finset.range K, (f k : ℝ) * (l : ℝ) ^ (k + 1) ≤ w + δ * (l : ℝ) ^ (k + 1)) :
    (∑ k ∈ Finset.range K, (f k : ℝ)) ≤ w / ((l : ℝ) - 1) + δ * K := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : ∀ k ∈ Finset.range K, (f k : ℝ) ≤ w * (1 / (l : ℝ) ^ (k + 1)) + δ := by
    intro k hk
    have hp : (0 : ℝ) < (l : ℝ) ^ (k + 1) := pow_pos (by linarith) _
    have h3 := hf k hk
    have h2 : w * (1 / (l : ℝ) ^ (k + 1)) + δ = (w + δ * (l : ℝ) ^ (k + 1)) / (l : ℝ) ^ (k + 1) := by
      first
        | (field_simp; ring)
        | field_simp
        | (rw [eq_div_iff hp.ne', add_mul, mul_assoc, one_div, inv_mul_cancel₀ hp.ne', mul_one])
    rw [h2]
    first
      | (rw [le_div_iff₀ hp]; exact h3)
      | (rw [le_div_iff hp]; exact h3)
  calc (∑ k ∈ Finset.range K, (f k : ℝ))
        ≤ ∑ k ∈ Finset.range K, (w * (1 / (l : ℝ) ^ (k + 1)) + δ) := Finset.sum_le_sum h1
    _ = w * ∑ k ∈ Finset.range K, (1 / (l : ℝ) ^ (k + 1)) + δ * K := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ w * (1 / ((l : ℝ) - 1)) + δ * K := by
        have := mul_le_mul_of_nonneg_left (geom_sum_inv_pow_succ_le_inv_sub_one (l : ℝ) hl' K) hw
        linarith
    _ = w / ((l : ℝ) - 1) + δ * K := by rw [mul_one_div]

private theorem natLog_le_logb_of_one_le_of_two_le (l : ℕ) (hl : 2 ≤ l) (N : ℕ) (hN : 1 ≤ N) :
    (Nat.log l N : ℝ) ≤ Real.logb l N := by
  have hpow : l ^ Nat.log l N ≤ N := Nat.pow_log_le_self l (by omega)
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpow' : (l : ℝ) ^ Nat.log l N ≤ N := by exact_mod_cast hpow
  first
    | (rw [Real.le_logb_iff_rpow_le hl1 hN', Real.rpow_natCast]; exact hpow')
    | exact (Real.le_logb_iff_rpow_le hl1 hN').2 (by simpa using hpow')
    | exact (le_of_eq (by rw [Real.logb_pow, Real.logb_self_eq_one hl1, mul_one] : (Nat.log l N : ℝ) = Real.logb l ((l : ℝ) ^ Nat.log l N))).trans (Real.logb_le_logb_of_le hl1 (pow_pos (by linarith) _) hpow')

theorem lemmaG_exp (l : ℕ) [Fact l.Prime] (a S η b : ℕ) (ha : 1 ≤ a) (hb : 2 * a + η + 1 ≤ b)
    (S₂ : Finset ℤ)
    (hS₂ : S₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (m : ℤ) (hm : m ∈ Finset.Icc ((b : ℤ) - a + 1) b) :
    (((∑ m' ∈ (Finset.Icc ((b : ℤ) - a + 1) b).erase m, padicValInt l (m - m')) +
        ∑ m' ∈ S₂, padicValInt l (m - m') : ℕ) : ℝ) ≤
      ((3 * a + S + 2 * η : ℕ) - 2 : ℝ) / ((l : ℝ) - 1) + Real.logb l ((b : ℝ) + η - 1) := by
  have hl2 : 2 ≤ l := (Fact.out : Nat.Prime l).two_le
  have hm' := hm
  rw [Finset.mem_Icc] at hm'
  obtain ⟨hm1, hm2⟩ := hm'
  obtain ⟨AA, hAA⟩ : ∃ s : Finset ℤ, s = Finset.Icc ((b : ℤ) - a + 1) ((b : ℤ) + S + a) := ⟨_, rfl⟩
  obtain ⟨IB, hIB⟩ : ∃ s : Finset ℤ, s = Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) := ⟨_, rfl⟩
  have hsplit : (∑ m' ∈ (Finset.Icc ((b : ℤ) - a + 1) b).erase m, padicValInt l (m - m')) +
        ∑ m' ∈ S₂, padicValInt l (m - m') ≤
      (∑ m' ∈ AA.erase m, padicValInt l (m - m')) + ∑ m' ∈ IB, padicValInt l (m - m') := by
    have hdisj : Disjoint (Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a)) IB := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      rw [hIB, Finset.mem_Icc] at hy'
      rw [Finset.mem_Icc] at hy
      omega
    have h1 : ∑ m' ∈ S₂, padicValInt l (m - m') ≤
        (∑ m' ∈ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a), padicValInt l (m - m')) +
          ∑ m' ∈ IB, padicValInt l (m - m') := by
      rw [← Finset.sum_union hdisj]
      apply Finset.sum_le_sum_of_subset
      rw [hIB]
      exact hS₂
    have hdisj2 : Disjoint ((Finset.Icc ((b : ℤ) - a + 1) b).erase m)
        (Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a)) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      rw [Finset.mem_erase, Finset.mem_Icc] at hy
      rw [Finset.mem_Icc] at hy'
      omega
    have h2 : AA.erase m = (Finset.Icc ((b : ℤ) - a + 1) b).erase m ∪
        Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) := by
      rw [hAA]
      ext y
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
      omega
    rw [h2, Finset.sum_union hdisj2]
    omega
  have hfA : ∀ k ∈ Finset.range (Nat.log l (S + 2 * a)),
      ((((AA.erase m).filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).card : ℕ) : ℝ) * (l : ℝ) ^ (k + 1) ≤
        ((S : ℝ) + 2 * a - 1) + 0 * (l : ℝ) ^ (k + 1) := by
    intro k _
    have hq : (0 : ℤ) < (l : ℤ) ^ (k + 1) := pow_pos (by exact_mod_cast (by omega : 0 < l)) _
    have h1 := card_filter_dvd_sub_mul_le_Icc_length_add ((l : ℤ) ^ (k + 1)) hq ((b : ℤ) - a + 1) ((b : ℤ) + S + a) m
      (by omega)
    rw [← hAA] at h1
    have hmem : m ∈ AA.filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t) := by
      rw [Finset.mem_filter, hAA, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, by rw [sub_self]; exact dvd_zero _⟩
    have hfe : (AA.erase m).filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t) =
        (AA.filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).erase m := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    have hc := Finset.card_erase_add_one hmem
    rw [← hfe] at hc
    rw [← hc] at h1
    generalize ((AA.erase m).filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).card = c' at h1 ⊢
    have h3 := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at h3
    linarith
  have hfB : ∀ k ∈ Finset.range (Nat.log l (b + η - 1)),
      (((IB.filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).card : ℕ) : ℝ) * (l : ℝ) ^ (k + 1) ≤
        (2 * (η : ℝ) + a - 1) + 1 * (l : ℝ) ^ (k + 1) := by
    intro k _
    have hq : (0 : ℤ) < (l : ℤ) ^ (k + 1) := pow_pos (by exact_mod_cast (by omega : 0 < l)) _
    have h1 := card_filter_dvd_sub_mul_le_Icc_length_add ((l : ℤ) ^ (k + 1)) hq (1 - (η : ℤ)) ((η : ℤ) + a) m (by omega)
    rw [← hIB] at h1
    generalize (IB.filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).card = c' at h1 ⊢
    have h3 := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at h3
    linarith
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hη' : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hS' : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hA : ((∑ m' ∈ AA.erase m, padicValInt l (m - m') : ℕ) : ℝ) ≤
      ((S : ℝ) + 2 * a - 1) / ((l : ℝ) - 1) := by
    rw [sum_padicValInt_sub_eq_sum_card_filter_pow_dvd l (S + 2 * a) m (AA.erase m) (by
      intro t ht
      rw [Finset.mem_erase, hAA, Finset.mem_Icc] at ht
      exact ⟨ht.1, by omega⟩), Nat.cast_sum]
    have hK := sum_card_le_div_sub_one_add_mul_of_mul_pow_le l hl2 (Nat.log l (S + 2 * a)) ((S : ℝ) + 2 * a - 1) (by linarith) 0
      (fun k => ((AA.erase m).filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).card) hfA
    refine le_trans hK ?_
    linarith
  have hB : ((∑ m' ∈ IB, padicValInt l (m - m') : ℕ) : ℝ) ≤
      (2 * (η : ℝ) + a - 1) / ((l : ℝ) - 1) + Real.logb l ((b : ℝ) + η - 1) := by
    rw [sum_padicValInt_sub_eq_sum_card_filter_pow_dvd l (b + η - 1) m IB (by
      intro t ht
      rw [hIB, Finset.mem_Icc] at ht
      exact ⟨by omega, by omega⟩), Nat.cast_sum]
    have hK := sum_card_le_div_sub_one_add_mul_of_mul_pow_le l hl2 (Nat.log l (b + η - 1)) (2 * (η : ℝ) + a - 1) (by linarith) 1
      (fun k => (IB.filter (fun t => (l : ℤ) ^ (k + 1) ∣ m - t)).card) hfB
    have hlog := natLog_le_logb_of_one_le_of_two_le l hl2 (b + η - 1) (by omega)
    have hcast : ((b + η - 1 : ℕ) : ℝ) = (b : ℝ) + η - 1 := by
      have h : 1 ≤ b + η := by omega
      rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]
    rw [hcast] at hlog
    refine le_trans hK ?_
    linarith
  have hnum : ((S : ℝ) + 2 * a - 1) + (2 * (η : ℝ) + a - 1) = ((3 * a + S + 2 * η : ℕ) - 2 : ℝ) := by
    push_cast
    ring
  calc _ ≤ ((∑ m' ∈ AA.erase m, padicValInt l (m - m') : ℕ) : ℝ) +
          ((∑ m' ∈ IB, padicValInt l (m - m') : ℕ) : ℝ) := by exact_mod_cast hsplit
    _ ≤ ((S : ℝ) + 2 * a - 1) / ((l : ℝ) - 1) +
          ((2 * (η : ℝ) + a - 1) / ((l : ℝ) - 1) + Real.logb l ((b : ℝ) + η - 1)) := add_le_add hA hB
    _ = ((3 * a + S + 2 * η : ℕ) - 2 : ℝ) / ((l : ℝ) - 1) + Real.logb l ((b : ℝ) + η - 1) := by
        rw [← add_assoc, ← add_div, hnum]

theorem lemmaG_lagr (l : ℕ) [Fact l.Prime] {O : Type*} [CommRing O] [IsDomain O]
    {V : Type*} [AddCommGroup V] [Module O V] (T : Module.End O V) (c : ℤ → O) (hl0 : (l : O) ≠ 0)
    (hc : ∀ j j' : ℤ, j ≠ j' → Associated (c j - c j') ((l : O) ^ padicValInt l (j - j')))
    (a S η b E : ℕ) (ha : 1 ≤ a) (hb : 2 * a + η + 1 ≤ b) (S₂ : Finset ℤ)
    (hS₂ : S₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (x : V)
    (h₁ : aeval T (∏ j ∈ Finset.range a, (X - C (c ((b : ℤ) - j)))) x = 0)
    (h₂ : aeval T (∏ m ∈ S₂, (X - C (c m))) x = 0)
    (hE : ⌊((3 * a + S + 2 * η : ℕ) - 2 : ℝ) / ((l : ℝ) - 1) + Real.logb l ((b : ℝ) + η - 1)⌋₊ ≤ E) :
    ((l : O) ^ E) • x = 0 := by
  have hS₁ : (Finset.range a).image (fun j : ℕ => (b : ℤ) - j) = Finset.Icc ((b : ℤ) - a + 1) b := by
    ext y
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · intro hy
      exact ⟨(b - y).toNat, by omega, by omega⟩
  have hprod : (∏ j ∈ Finset.range a, (X - C (c ((b : ℤ) - j)))) =
      ∏ m ∈ Finset.Icc ((b : ℤ) - a + 1) b, (X - C (c m)) := by
    rw [← hS₁, Finset.prod_image]
    intro i _ j _ hij
    have hij' : (b : ℤ) - i = (b : ℤ) - j := hij
    omega
  rw [hprod] at h₁
  refine smul_eq_zero_of_aeval_prod T (Finset.Icc ((b : ℤ) - a + 1) b) S₂ c ((l : O) ^ E) x ?_ ?_ h₁ h₂ ?_
  · rw [Finset.disjoint_left]
    intro y hy hy2
    have h := hS₂ hy2
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at h
    rw [Finset.mem_Icc] at hy
    omega
  · intro j _ j' _ hjj
    by_contra hne
    have h := hc j j' hne
    rw [hjj, sub_self] at h
    exact pow_ne_zero _ hl0 (h.eq_zero_iff.mp rfl)
  · intro m hm
    have hsum := lemmaG_exp l a S η b ha hb S₂ hS₂ m hm
    have hle : (∑ m' ∈ (Finset.Icc ((b : ℤ) - a + 1) b).erase m, padicValInt l (m - m')) +
        ∑ m' ∈ S₂, padicValInt l (m - m') ≤ E := le_trans (Nat.le_floor hsum) hE
    have hmS₂ : m ∉ S₂ := by
      intro h
      have h' := hS₂ h
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at h'
      rw [Finset.mem_Icc] at hm
      omega
    have hd1 : (∏ m' ∈ (Finset.Icc ((b : ℤ) - a + 1) b).erase m, (c m - c m')) ∣
        (l : O) ^ (∑ m' ∈ (Finset.Icc ((b : ℤ) - a + 1) b).erase m, padicValInt l (m - m')) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_dvd_prod_of_dvd
      intro m' hm'
      exact (hc m m' (Finset.ne_of_mem_erase hm').symm).dvd
    have hd2 : (∏ m' ∈ S₂, (c m - c m')) ∣ (l : O) ^ (∑ m' ∈ S₂, padicValInt l (m - m')) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_dvd_prod_of_dvd
      intro m' hm'
      exact (hc m m' (fun h => hmS₂ (h ▸ hm'))).dvd
    calc _ ∣ (l : O) ^ (∑ m' ∈ (Finset.Icc ((b : ℤ) - a + 1) b).erase m, padicValInt l (m - m')) *
          (l : O) ^ (∑ m' ∈ S₂, padicValInt l (m - m')) := mul_dvd_mul hd1 hd2
      _ = (l : O) ^ ((∑ m' ∈ (Finset.Icc ((b : ℤ) - a + 1) b).erase m, padicValInt l (m - m')) +
          ∑ m' ∈ S₂, padicValInt l (m - m')) := (pow_add _ _ _).symm
      _ ∣ (l : O) ^ E := pow_dvd_pow _ hle

end Formalism.MainNotions.N.FrobeniusPowerSeries
