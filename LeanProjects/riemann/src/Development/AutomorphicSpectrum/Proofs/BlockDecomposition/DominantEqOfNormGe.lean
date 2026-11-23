import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.LemmaH

theorem two_sum_Ico (a d : ℕ) :
    2 * ∑ i ∈ Finset.Ico a (a + d), (i : ℝ) = d * (2 * a + d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), mul_add, ih]
    push_cast
    ring

theorem sum_le_top (A : Finset ℕ) : ∀ t : ℕ, (∀ a ∈ A, a < t) →
    2 * ∑ i ∈ A, (i : ℝ) + (A.card : ℝ) * ((A.card : ℝ) + 1) ≤ 2 * (A.card : ℝ) * t := by
  induction A using Finset.induction_on_max with
  | empty => intro t _; simp
  | insert a A hA ih =>
    intro t ht
    have hnot : a ∉ A := fun h => lt_irrefl _ (hA a h)
    have h1 := ih a hA
    have h2 : (a : ℝ) + 1 ≤ t := by exact_mod_cast ht a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hnot, Finset.card_insert_of_notMem hnot]
    push_cast
    have hc : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    nlinarith [mul_nonneg (add_nonneg hc zero_le_one) (sub_nonneg.2 h2)]

theorem alg_core (R U c0 Pa SA SB Ls L1 L2 G1 GA : ℝ) (hR : 0 < R) (hU : 0 < U)
    (h1 : SA ≤ R * c0) (h2 : U * (c0 - (R + U - 1)) ≤ SB) (h3 : Pa + SA + SB ≤ Ls + L1 + L2)
    (h4 : Pa ≤ Ls) (hE : GA ≤ G1 + R * U) (hC : R * L2 + 2 * R * U * (R + U) ≤ U * L1) :
    Pa + SA + GA ≤ Ls + L1 + G1 := by
  have hN : 0 < R + U := add_pos hR hU
  have a1 := mul_le_mul_of_nonneg_left h4 hU.le
  have a2 := mul_le_mul_of_nonneg_left h3 hR.le
  have a3 := mul_le_mul_of_nonneg_left h1 hU.le
  have a4 := mul_le_mul_of_nonneg_left h2 hR.le
  have a5 := mul_le_mul_of_nonneg_left hE hN.le
  have a6 := (mul_pos hR hU).le
  have key : (R + U) * (Pa + SA + GA) ≤ (R + U) * (Ls + L1 + G1) := by
    nlinarith [a1, a2, a3, a4, a5, a6, hC]
  exact le_of_mul_le_mul_left key hN

theorem core (n k : ℕ) (ν c : ℕ → ℝ)
    (hν : ∀ i j, i ≤ j → j < n → ν j ≤ ν i)
    (hc : ∀ i j, i ≤ j → j < n → c j ≤ c i)
    (hP : ∀ j, j ≤ n → ∑ i ∈ Finset.range j, ν i ≤ ∑ i ∈ Finset.range j, (c i - 4 * (i : ℝ)))
    (I : Finset ℕ) (hI : ∀ i ∈ I, i < n) (hk : I.card = k)
    (htop : ∀ a ∈ I, ∀ b, b < n → b ∉ I → ν b + b ≤ ν a + a) :
    ∑ i ∈ I, (ν i + (i : ℝ)) ≤ ∑ i ∈ Finset.range k, (c i - 4 * (i : ℝ) + (i : ℝ)) := by
  classical
  have hkn : k ≤ n := by
    have hsub : I ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hI i hi)
    simpa [hk] using Finset.card_le_card hsub
  by_cases hEq : I = Finset.range k
  · rw [hEq, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have := hP k hkn
    linarith
  have hb : ∃ b, b < k ∧ b ∉ I := by
    by_contra hcon
    push_neg at hcon
    apply hEq
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      exact hcon i (Finset.mem_range.1 hi)
    · simp [hk]
  have ha : ∃ a ∈ I, k ≤ a := by
    by_contra hcon
    push_neg at hcon
    apply hEq
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      exact Finset.mem_range.2 (hcon i hi)
    · simp [hk]
  obtain ⟨b, hbk, hbI⟩ := hb
  obtain ⟨a, haI, hka⟩ := ha
  obtain ⟨s, hsI, hlt, hsb⟩ : ∃ s, s ∉ I ∧ (∀ i, i < s → i ∈ I) ∧ s ≤ b := by
    have hex : ∃ b, b ∉ I := ⟨b, hbI⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_, Nat.find_min' hex hbI⟩
    have := Nat.find_min hex hi
    simpa using this
  obtain ⟨e, heI, hle⟩ : ∃ e, e ∈ I ∧ ∀ i ∈ I, i ≤ e :=
    ⟨I.max' ⟨a, haI⟩, Finset.max'_mem _ _, fun i hi => Finset.le_max' _ _ hi⟩
  have hae : a ≤ e := hle a haI
  have hen : e < n := hI e heI
  obtain ⟨r, hr⟩ : ∃ r, k = s + r := ⟨k - s, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, e + 1 = s + r + u := ⟨e + 1 - (s + r), by omega⟩
  have hr1 : 1 ≤ r := by omega
  have hu1 : 1 ≤ u := by omega
  subst hr
  have hsplit : ∀ f : ℕ → ℝ, ∑ i ∈ I, f i =
      ∑ i ∈ Finset.range s, f i + ∑ i ∈ I.filter (fun i => s ≤ i), f i := by
    intro f
    have hnot : I.filter (fun i => ¬ s ≤ i) = Finset.range s := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, not_le]
      exact ⟨fun h => h.2, fun h => ⟨hlt i h, h⟩⟩
    rw [← Finset.sum_filter_add_sum_filter_not I (fun i => s ≤ i) f, hnot, add_comm]
  set A := I.filter (fun i => s ≤ i) with hA
  have hcardA : (A.card : ℝ) = r := by
    have h := hsplit (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range, hk] at h
    push_cast at h
    linarith
  have hAsub : A ⊆ Finset.Ico s (s + r + u) := by
    intro i hi
    have hi' := Finset.mem_filter.1 hi
    have := hle i hi'.1
    exact Finset.mem_Ico.2 ⟨hi'.2, by omega⟩
  set B := Finset.Ico s (s + r + u) \ A with hB
  have hD : ∀ f : ℕ → ℝ, ∑ i ∈ B, f i + ∑ i ∈ A, f i = ∑ i ∈ Finset.Ico s (s + r + u), f i :=
    fun f => Finset.sum_sdiff hAsub
  have hcardB : (B.card : ℝ) = u := by
    have h := hD (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico] at h
    have h2 : ((s + r + u - s : ℕ) : ℝ) = r + u := by
      have : s + r + u - s = r + u := by omega
      rw [this]; push_cast; ring
    rw [h2, hcardA] at h
    linarith
  have hRpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hUpos : (0 : ℝ) < u := by exact_mod_cast hu1
  have he : (e : ℝ) = s + r + u - 1 := by
    have : ((e + 1 : ℕ) : ℝ) = ((s + r + u : ℕ) : ℝ) := by rw [hu]
    push_cast at this
    linarith

  have h1 : ∑ i ∈ A, ν i ≤ r * ν s := by
    have := Finset.sum_le_card_nsmul A ν (ν s) (fun i hi => by
      have hi' := Finset.mem_filter.1 hi
      exact hν s i hi'.2 (hI i hi'.1))
    rwa [nsmul_eq_mul, hcardA] at this
  have hF := htop e heI s (by have := hle e heI; omega) hsI
  have h2 : (u : ℝ) * (ν s - ((r : ℝ) + u - 1)) ≤ ∑ i ∈ B, ν i := by
    have h := Finset.card_nsmul_le_sum B ν (ν e) (fun i hi => by
      have hi' := Finset.mem_Ico.1 (Finset.mem_sdiff.1 hi).1
      exact hν i e (by omega) hen)
    rw [nsmul_eq_mul, hcardB] at h
    refine le_trans ?_ h
    apply mul_le_mul_of_nonneg_left _ hUpos.le
    linarith
  have hsn : s ≤ n := by omega
  have htn : s + r + u ≤ n := by omega
  have hkn' : s + r ≤ n := by omega
  have hIco := Finset.sum_Ico_eq_sub ν (show s ≤ s + r + u by omega)
  have h3 : ∑ i ∈ Finset.range s, ν i + ∑ i ∈ A, ν i + ∑ i ∈ B, ν i ≤
      ∑ i ∈ Finset.range (s + r + u), (c i - 4 * (i : ℝ)) := by
    have := hP _ htn
    have h' := hD ν
    linarith
  have h4 := hP s hsn
  set M : ℕ → ℝ := fun i => c i - 4 * (i : ℝ) with hM
  have hL1 := Finset.sum_Ico_eq_sub M (show s ≤ s + r by omega)
  have hL2 := Finset.sum_Ico_eq_sub M (show s + r ≤ s + r + u by omega)
  have hG1 := Finset.sum_Ico_eq_sub (fun i : ℕ => (i : ℝ)) (show s ≤ s + r by omega)
  have t1 := two_sum_Ico s r
  have t2 := two_sum_Ico (s + r) u
  have t3 := sum_le_top A (s + r + u) (fun i hi => Finset.mem_Ico.1 (hAsub hi) |>.2)
  rw [hcardA] at t3
  push_cast at t2 t3
  have hE : ∑ i ∈ A, (i : ℝ) ≤ ∑ i ∈ Finset.Ico s (s + r), (i : ℝ) + r * u := by
    nlinarith [t1, t3]
  have hckn : s + r < n := by omega
  have hc1 : (r : ℝ) * c (s + r) ≤ ∑ i ∈ Finset.Ico s (s + r), c i := by
    have h := Finset.card_nsmul_le_sum (Finset.Ico s (s + r)) c (c (s + r)) (fun i hi => by
      have hi' := Finset.mem_Ico.1 hi
      exact hc i (s + r) (by omega) hckn)
    simpa [nsmul_eq_mul, Nat.card_Ico] using h
  have hc2 : ∑ i ∈ Finset.Ico (s + r) (s + r + u), c i ≤ (u : ℝ) * c (s + r) := by
    have h := Finset.sum_le_card_nsmul (Finset.Ico (s + r) (s + r + u)) c (c (s + r)) (fun i hi => by
      have hi' := Finset.mem_Ico.1 hi
      exact hc (s + r) i hi'.1 (by omega))
    simpa [nsmul_eq_mul, Nat.card_Ico] using h
  have hM1 : ∑ i ∈ Finset.Ico s (s + r), M i =
      ∑ i ∈ Finset.Ico s (s + r), c i - 4 * ∑ i ∈ Finset.Ico s (s + r), (i : ℝ) := by
    simp only [hM, Finset.sum_sub_distrib, Finset.mul_sum]
  have hM2 : ∑ i ∈ Finset.Ico (s + r) (s + r + u), M i =
      ∑ i ∈ Finset.Ico (s + r) (s + r + u), c i - 4 * ∑ i ∈ Finset.Ico (s + r) (s + r + u), (i : ℝ) := by
    simp only [hM, Finset.sum_sub_distrib, Finset.mul_sum]
  have hC : (r : ℝ) * ∑ i ∈ Finset.Ico (s + r) (s + r + u), M i + 2 * r * u * (r + u) ≤
      (u : ℝ) * ∑ i ∈ Finset.Ico s (s + r), M i := by
    rw [hM1, hM2]
    have b1 := mul_le_mul_of_nonneg_left hc1 hUpos.le
    have b2 := mul_le_mul_of_nonneg_left hc2 hRpos.le
    nlinarith [b1, b2, t1, t2]
  have fin := alg_core r u (ν s) (∑ i ∈ Finset.range s, ν i) (∑ i ∈ A, ν i) (∑ i ∈ B, ν i)
    (∑ i ∈ Finset.range s, M i) (∑ i ∈ Finset.Ico s (s + r), M i)
    (∑ i ∈ Finset.Ico (s + r) (s + r + u), M i)
    (∑ i ∈ Finset.Ico s (s + r), (i : ℝ)) (∑ i ∈ A, (i : ℝ)) hRpos hUpos h1 h2
    (by rw [hL1, hL2]; linarith) h4 hE hC
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hL1] at fin
  rw [hG1] at fin
  linarith

theorem abel (z d : ℕ → ℝ) (N : ℕ) (hz : ∀ i, i < N → 1 ≤ z i - z (i + 1))
    (hD : ∀ j, j ≤ N + 1 → 0 ≤ ∑ i ∈ Finset.range j, d i) :
    ∀ m, m ≤ N → z m * ∑ i ∈ Finset.range (m + 1), d i +
      ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1), d i ≤ ∑ i ∈ Finset.range (m + 1), z i * d i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hzz := hz m (by omega)
    have hD0 := hD (m + 1) (by omega)
    have e1 : ∑ i ∈ Finset.range (m + 1 + 1), d i = ∑ i ∈ Finset.range (m + 1), d i + d (m + 1) :=
      Finset.sum_range_succ _ _
    have e2 : ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (j + 1), d i =
        ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1), d i + ∑ i ∈ Finset.range (m + 1), d i :=
      Finset.sum_range_succ _ _
    have e3 : ∑ i ∈ Finset.range (m + 1 + 1), z i * d i =
        ∑ i ∈ Finset.range (m + 1), z i * d i + z (m + 1) * d (m + 1) :=
      Finset.sum_range_succ _ _
    rw [e1, e2, e3]
    nlinarith [mul_nonneg (sub_nonneg.2 hzz) hD0]

theorem eq_of_dom (N : ℕ) (m y : ℕ → ℝ)
    (hs : ∀ i, i < N → 1 ≤ (m i + y i) - (m (i + 1) + y (i + 1)))
    (hdom : ∀ j, j ≤ N + 1 → ∑ i ∈ Finset.range j, y i ≤ ∑ i ∈ Finset.range j, m i)
    (htot : ∑ i ∈ Finset.range (N + 1), y i = ∑ i ∈ Finset.range (N + 1), m i)
    (hsq : ∑ i ∈ Finset.range (N + 1), (m i) ^ 2 ≤ ∑ i ∈ Finset.range (N + 1), (y i) ^ 2) :
    ∀ i, i < N + 1 → y i = m i := by
  set d : ℕ → ℝ := fun i => m i - y i with hd
  have hDsum : ∀ j, ∑ i ∈ Finset.range j, d i = ∑ i ∈ Finset.range j, m i - ∑ i ∈ Finset.range j, y i := by
    intro j
    simp only [hd, Finset.sum_sub_distrib]
  have hD : ∀ j, j ≤ N + 1 → 0 ≤ ∑ i ∈ Finset.range j, d i := by
    intro j hj
    rw [hDsum]
    linarith [hdom j hj]
  have hDN : ∑ i ∈ Finset.range (N + 1), d i = 0 := by
    rw [hDsum, htot]; ring
  have hab := abel (fun i => m i + y i) d N hs hD N le_rfl
  rw [hDN, mul_zero, zero_add] at hab
  have hzd : ∑ i ∈ Finset.range (N + 1), (m i + y i) * d i ≤ 0 := by
    have : ∑ i ∈ Finset.range (N + 1), (m i + y i) * d i =
        ∑ i ∈ Finset.range (N + 1), (m i) ^ 2 - ∑ i ∈ Finset.range (N + 1), (y i) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [hd]; ring
    rw [this]
    linarith
  have hz0 : ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), d i = 0 :=
    le_antisymm (le_trans hab hzd) (Finset.sum_nonneg fun j hj => hD _ (by
      have := Finset.mem_range.1 hj
      omega))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hD _ (by
      have := Finset.mem_range.1 hj
      omega))).1 hz0
  have hzero : ∀ j, j ≤ N + 1 → ∑ i ∈ Finset.range j, d i = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    rcases Nat.lt_or_ge j (N + 1) with h | h
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact hall j' (Finset.mem_range.2 (by omega))
    · have : j = N + 1 := by omega
      rw [this]; exact hDN
  intro i hi
  have h1 := hzero i (by omega)
  have h2 := hzero (i + 1) (by omega)
  rw [Finset.sum_range_succ, h1, zero_add] at h2
  simp only [hd] at h2
  linarith

variable {n : ℕ}

def ex (f : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then f ⟨i, h⟩ else 0

theorem ex_mk (f : Fin n → ℝ) {i : ℕ} (h : i < n) : ex f i = f ⟨i, h⟩ := dif_pos h

theorem ex_val (f : Fin n → ℝ) (a : Fin n) : ex f (a : ℕ) = f a := by
  rw [ex_mk f a.2]

theorem map_filter_lt {k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun a : Fin n => (a : ℕ) < k)).map Fin.valEmbedding = Finset.range k := by
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hi
    exact ⟨⟨i, by omega⟩, hi, rfl⟩

theorem card_filter_lt {k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun a : Fin n => (a : ℕ) < k)).card = k := by
  have := congrArg Finset.card (map_filter_lt hk)
  simpa using this

theorem sum_range_of (f : Fin n → ℝ) (G : ℕ → ℝ) {k : ℕ} (hk : k ≤ n)
    (hG : ∀ a : Fin n, G a = f a) :
    ∑ i ∈ Finset.range k, G i = ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), f a := by
  rw [← map_filter_lt hk, Finset.sum_map]
  exact Finset.sum_congr rfl fun a _ => hG a

theorem lam_add (lam : Fin n → ℤ) (hl : StrictAnti lam) :
    ∀ (d i : ℕ) (h : i + d < n), lam ⟨i + d, h⟩ + d ≤ lam ⟨i, by omega⟩ := by
  intro d
  induction d with
  | zero => intro i h; simp
  | succ d ih =>
    intro i h
    have h1 := ih i (by omega)
    have h2 : lam ⟨i + (d + 1), h⟩ < lam ⟨i + d, by omega⟩ :=
      hl (Fin.mk_lt_mk.2 (by omega))
    push_cast
    omega

theorem lam_mono (lam : Fin n → ℤ) (hl : StrictAnti lam) {a b : Fin n} (hab : a ≤ b) :
    lam b + ((b : ℕ) : ℤ) ≤ lam a + ((a : ℕ) : ℤ) := by
  obtain ⟨d, hd⟩ : ∃ d, (b : ℕ) = a + d := ⟨b - a, by have := Fin.le_def.1 hab; omega⟩
  have h := lam_add lam hl d a (by have := b.2; omega)
  have hb : (⟨(a : ℕ) + d, by have := b.2; omega⟩ : Fin n) = b := Fin.ext hd.symm
  rw [hb] at h
  have ha : (⟨(a : ℕ), a.2⟩ : Fin n) = a := rfl
  rw [ha] at h
  rw [hd]
  push_cast
  omega

theorem step1 (lam : Fin n → ℤ) (hl : StrictAnti lam) (ν : Fin n → ℤ) (hν : Antitone ν)
    (hD : DomLE (wtR ν) (m0 lam)) (w : Equiv.Perm (Fin n))
    (hw : Antitone (fun a => wtR ν (w a) - rhoV n (w a))) {k : ℕ} (hk : k ≤ n) :
    ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), (wtR ν (w a) - rhoV n (w a)) ≤
      ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), (m0 lam a - rhoV n a) := by
  classical
  set F := univ.filter (fun a : Fin n => (a : ℕ) < k) with hF
  set c : Fin n → ℝ := fun a => m0 lam a + 4 * ((a : ℕ) : ℝ) with hcdef
  set I : Finset ℕ := (F.map w.toEmbedding).map Fin.valEmbedding with hIdef
  have hmem : ∀ b : Fin n, (b : ℕ) ∈ I ↔ ((w.symm b : Fin n) : ℕ) < k := by
    intro b
    simp only [hIdef, hF, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_toEmbedding, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, hx⟩
      have : w y = b := Fin.ext hx
      rw [← this]
      simpa using hy
    · intro h
      exact ⟨b, ⟨w.symm b, h, by simp⟩, rfl⟩
  have hcore := core n k (ex (wtR ν)) (ex c)
    (by
      intro i j hij hj
      rw [ex_mk _ hj, ex_mk _ (show i < n by omega)]
      have := hν (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hj⟩ from Fin.mk_le_mk.2 hij)
      simp only [wtR]
      exact_mod_cast this)
    (by
      intro i j hij hj
      rw [ex_mk _ hj, ex_mk _ (show i < n by omega)]
      have := lam_mono lam hl (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hj⟩ from Fin.mk_le_mk.2 hij)
      have h2 : ((lam ⟨j, hj⟩ : ℤ) : ℝ) + (j : ℝ) ≤ ((lam ⟨i, by omega⟩ : ℤ) : ℝ) + (i : ℝ) := by
        exact_mod_cast this
      simp only [hcdef, m0]
      linarith)
    (by
      intro j hj
      rw [sum_range_of (wtR ν) _ hj (fun a => ex_val _ a),
        sum_range_of (m0 lam) (fun i => ex c i - 4 * (i : ℝ)) hj
          (fun a => by simp only [ex_val, hcdef]; ring)]
      exact hD.1 j)
    I
    (by
      intro i hi
      simp only [hIdef, Finset.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2)
    (by simp [hIdef, hF, card_filter_lt hk])
    (by
      intro a ha b hb hbI
      have ha' : ∃ x : Fin n, (x : ℕ) = a := by
        simp only [hIdef, Finset.mem_map] at ha
        obtain ⟨x, _, hx⟩ := ha
        exact ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := ha'
      have hxk := (hmem x).1 ha
      have hbk : ¬ ((w.symm ⟨b, hb⟩ : Fin n) : ℕ) < k := fun h => hbI ((hmem ⟨b, hb⟩).2 h)
      have hle : w.symm x ≤ w.symm ⟨b, hb⟩ := Fin.le_def.2 (by omega)
      have := hw hle
      simp only [Equiv.apply_symm_apply, rhoV] at this
      rw [ex_val, ex_mk _ hb]
      linarith)
  have hL : ∑ i ∈ I, (ex (wtR ν) i + (i : ℝ)) = ∑ a ∈ F, (wtR ν (w a) + ((w a : ℕ) : ℝ)) := by
    simp only [hIdef, Finset.sum_map, Equiv.coe_toEmbedding, Fin.valEmbedding_apply, ex_val]
  have hR : ∑ i ∈ Finset.range k, (ex c i - 4 * (i : ℝ) + (i : ℝ)) =
      ∑ a ∈ F, (m0 lam a + ((a : ℕ) : ℝ)) :=
    sum_range_of (fun a => m0 lam a + ((a : ℕ) : ℝ)) _ hk
      (fun a => by simp only [ex_val, hcdef]; ring)
  rw [hL, hR] at hcore
  have e1 : ∑ a ∈ F, (wtR ν (w a) - rhoV n (w a)) =
      ∑ a ∈ F, (wtR ν (w a) + ((w a : ℕ) : ℝ)) - ∑ a ∈ F, (((n : ℝ) - 1) / 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [rhoV]; ring
  have e2 : ∑ a ∈ F, (m0 lam a - rhoV n a) =
      ∑ a ∈ F, (m0 lam a + ((a : ℕ) : ℝ)) - ∑ a ∈ F, (((n : ℝ) - 1) / 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [rhoV]; ring
  rw [e1, e2]
  linarith

end GlobalTheory.CompanionTheory.RealCount.LemmaH

namespace GlobalTheory.CompanionTheory.RealCount

end GlobalTheory.CompanionTheory.RealCount
