import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem parEps_eq_false_iff (k r : ℕ) (hk : 1 ≤ k) (b : Fin (2 * r + k + 1)) :
    parEps k r b = false ↔ k ≤ b.val ∧ (b.val - k) % 2 = 0 := by
  unfold parEps
  split_ifs with h
  · constructor
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      omega
  · simp only [decide_eq_false_iff_not]
    omega

theorem parEps_true_of_lt (k r : ℕ) (hk : 1 ≤ k) (b : Fin (2 * r + k + 1)) (hb : b.val < k) :
    parEps k r b = true := by
  cases h : parEps k r b
  · exact absurd ((parEps_eq_false_iff k r hk b).1 h).1 (by omega)
  · rfl

theorem card_parEps_false (k r : ℕ) (hk : 1 ≤ k) :
    (univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false).card = r + 1 := by
  have e : (univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false) =
      (univ : Finset (Fin (r + 1))).image
        (fun i => (⟨k + 2 * i.val, by have := i.isLt; omega⟩ : Fin (2 * r + k + 1))) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_image, parEps_eq_false_iff k r hk]
    constructor
    · rintro ⟨h1, h2⟩
      have := b.isLt
      refine ⟨⟨(b.val - k) / 2, by omega⟩, Fin.ext ?_⟩
      show k + 2 * ((b.val - k) / 2) = b.val
      omega
    · rintro ⟨i, rfl⟩
      show k ≤ k + 2 * i.val ∧ (k + 2 * i.val - k) % 2 = 0
      omega
  rw [e, card_image_of_injective]
  · simp
  · intro i j h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)

theorem one_le_noncompactRank_parabolicSign (k r : ℕ) (hk : 1 ≤ k) : 1 ≤ S7.q0 (parEps k r) := by
  unfold S7.q0
  refine le_min ?_ ?_
  · unfold pOf
    refine Finset.card_pos.2 ⟨⟨0, by omega⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    exact parEps_true_of_lt k r hk _ (by show 0 < k; omega)
  · unfold qOf
    rw [card_parEps_false k r hk]
    omega

theorem rhoN_parEps (k r : ℕ) (hk : 1 ≤ k) (a : Fin (2 * r + k + 1)) (ha : a.val < k) :
    rhoN (parEps k r) a = ((r : ℝ) + 1) / 2 := by
  have hea := parEps_true_of_lt k r hk a ha
  have e1 : (univ.filter fun b => a < b ∧ parEps k r b ≠ parEps k r a) =
      univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false := by
    ext b
    simp only [mem_filter, mem_univ, true_and, hea, ne_eq, Bool.not_eq_true]
    constructor
    · exact And.right
    · intro hb
      have := ((parEps_eq_false_iff k r hk b).1 hb).1
      exact ⟨show a.val < b.val by omega, hb⟩
  have e2 : (univ.filter fun b => b < a ∧ parEps k r b ≠ parEps k r a) = ∅ := by
    refine filter_eq_empty_iff.2 ?_
    rintro b - ⟨hba, hne⟩
    have : b.val < a.val := hba
    exact hne (by rw [parEps_true_of_lt k r hk b (by omega), hea])
  unfold rhoN
  rw [e1, e2, card_parEps_false k r hk, card_empty]
  push_cast
  ring

theorem rhoC_parEps (k r : ℕ) (hk : 1 ≤ k) (a : Fin (2 * r + k + 1)) (ha : a.val < k) :
    rhoC (parEps k r) a = ((r : ℝ) + k - 1 - 2 * (a.val : ℝ)) / 2 := by
  have hea := parEps_true_of_lt k r hk a ha
  have e1 : (univ.filter fun b => a < b ∧ parEps k r b = parEps k r a) =
      (Ioi a).filter fun b => parEps k r b = true := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_Ioi, hea]
  have e3 : ((Ioi a).filter fun b => ¬ parEps k r b = true) =
      univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_Ioi, Bool.not_eq_true]
    constructor
    · exact And.right
    · intro hb
      have := ((parEps_eq_false_iff k r hk b).1 hb).1
      exact ⟨show a.val < b.val by omega, hb⟩
  have e2 : (univ.filter fun b => b < a ∧ parEps k r b = parEps k r a) = Iio a := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_Iio, hea]
    constructor
    · exact And.left
    · intro hb
      have : b.val < a.val := hb
      exact ⟨hb, parEps_true_of_lt k r hk b (by omega)⟩
  have hsum := card_filter_add_card_filter_not (s := Ioi a) (p := fun b => parEps k r b = true)
  rw [e3, card_parEps_false k r hk, Fin.card_Ioi] at hsum
  have hC : ((univ.filter fun b => a < b ∧ parEps k r b = parEps k r a).card : ℝ) =
      (r : ℝ) + k - 1 - (a.val : ℝ) := by
    rw [e1]
    have := a.isLt
    have h2 : ((Ioi a).filter fun b => parEps k r b = true).card + a.val + 1 = r + k := by omega
    have h3 := congrArg (fun m : ℕ => (m : ℝ)) h2
    push_cast at h3
    linarith
  unfold rhoC
  rw [hC, e2, Fin.card_Iio]
  ring

theorem u_strictAnti (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hI : Interlaces k r u v b) : StrictAnti u := by
  have step : ∀ (i j : Fin k), j.val = i.val + 1 → u j < u i := by
    intro i j hij
    have hi : i.val < k - 1 := by have := j.isLt; omega
    obtain ⟨h1, h2⟩ := hI.1 ⟨i.val, hi⟩
    have : j = ⟨i.val + 1, by have := j.isLt; omega⟩ := Fin.ext hij
    rw [this]
    exact lt_trans h2 h1
  have gen : ∀ d : ℕ, ∀ (i j : Fin k), j.val = i.val + d + 1 → u j < u i := by
    intro d
    induction d with
    | zero => intro i j h; exact step i j (by omega)
    | succ d ih =>
      intro i j h
      have hm : i.val + d + 1 < k := by have := j.isLt; omega
      exact lt_trans (step ⟨i.val + d + 1, hm⟩ j (by show j.val = i.val + d + 1 + 1; omega))
        (ih i ⟨i.val + d + 1, hm⟩ rfl)
  intro i j hij
  have : i.val < j.val := hij
  exact gen (j.val - i.val - 1) i j (by omega)

theorem u_isHCParam (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (hP : IsHCPar (parLam k r v b)) (hI : Interlaces k r u v b)
    (hH : HalfInts k r u v b) : Formalism.QuantumDeterminants.IsHCParam u := by
  refine ⟨u_strictAnti k r u v b hI, fun i => ?_⟩
  let s : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  obtain ⟨m1, hm1⟩ := hH i s
  obtain ⟨m2, hm2⟩ := hP.2 s
  refine ⟨m1 + m2 + r + 1, ?_⟩
  push_cast at hm2 ⊢
  linarith

theorem lamT_eq_sub (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ)
    (a : Fin (2 * r + k + 1)) :
    lamT k r u b t a = lamT k r u b 0 a - ((a.val + 1 - k : ℕ) : ℝ) * (t : ℝ) := by
  unfold lamT
  split_ifs with h
  · have : a.val + 1 - k = 0 := by omega
    simp [this]
  · have : a.val - (k - 1) = a.val + 1 - k := by omega
    have e : ((a.val - (k - 1) : ℕ) : ℝ) = ((a.val + 1 - k : ℕ) : ℝ) := by rw [this]
    rw [e]
    simp

theorem lamT_eq_parLam (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (t : ℕ) (a : Fin (2 * r + k + 1)) (ha : k ≤ a.val) :
    lamT k r u b t a = parLam k r v b a - ((a.val + 1 - k : ℕ) : ℝ) * (t : ℝ) := by
  unfold lamT parLam
  rw [dif_neg (by omega), dif_neg (by omega)]
  have : a.val - (k - 1) = a.val + 1 - k := by omega
  have e : ((a.val - (k - 1) : ℕ) : ℝ) = ((a.val + 1 - k : ℕ) : ℝ) := by rw [this]
  rw [e]

theorem lowK_lamT_affine (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ) :
    lowK (parEps k r) (lamT k r u b t) = (t : ℝ) • dNode k r + lowK (parEps k r) (lamT k r u b 0) := by
  funext a
  simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [lamT_eq_sub k r hk u b t a]
  have hd : dNode k r a = -((a.val + 1 - k : ℕ) : ℝ) := by
    unfold dNode
    split_ifs with h
    · have : a.val + 1 - k = 0 := by omega
      rw [this]
      simp
    · rfl
  rw [hd]
  ring

theorem lowK_lamT_first (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ)
    (a : Fin k) :
    lowK (parEps k r) (lamT k r u b t) ⟨a.val, by omega⟩ = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u a := by
  have ha : (⟨a.val, by omega⟩ : Fin (2 * r + k + 1)).val < k := a.isLt
  have hN0 : Formalism.REAL.rhoN (Formalism.MainNotions.S.allPos k) a = 0 := by
    simp [Formalism.REAL.rhoN, Formalism.MainNotions.S.allPos]
  have e1 : (univ.filter fun b : Fin k => a < b ∧ Formalism.MainNotions.S.allPos k b = Formalism.MainNotions.S.allPos k a) =
      Ioi a := by
    ext b; simp [Formalism.MainNotions.S.allPos]
  have e2 : (univ.filter fun b : Fin k => b < a ∧ Formalism.MainNotions.S.allPos k b = Formalism.MainNotions.S.allPos k a) =
      Iio a := by
    ext b; simp [Formalism.MainNotions.S.allPos]
  have hC0 : Formalism.REAL.rhoC (Formalism.MainNotions.S.allPos k) a = (((k : ℝ) - 1) - 2 * (a.val : ℝ)) / 2 := by
    have hc : ((k - 1 - (a : ℕ) : ℕ) : ℝ) = (k : ℝ) - 1 - (a : ℕ) := by
      have := a.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub hk]; simp
    unfold Formalism.REAL.rhoC
    rw [e1, e2, Fin.card_Ioi, Fin.card_Iio, hc]
    ring
  simp only [lowK, Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply]
  rw [rhoN_parEps k r hk _ ha, rhoC_parEps k r hk _ ha, hN0, hC0]
  simp only [lamT, a.isLt, ↓reduceDIte]
  ring

theorem lamT_facts : LamTStatement := by
  intro k r u v b hk hP hI hH
  refine ⟨u_isHCParam k r hk u v b hP hI hH, one_le_noncompactRank_parabolicSign k r hk,
    fun t => lowK_lamT_affine k r hk u b t, fun t a => lowK_lamT_first k r hk u b t a, ?_⟩
  set B : ℝ := ∑ a, |lamT k r u b 0 a| with hB
  have hBa : ∀ a, |lamT k r u b 0 a| ≤ B := fun a =>
    single_le_sum (f := fun a => |lamT k r u b 0 a|) (fun i _ => abs_nonneg _) (mem_univ a)
  have hB0 : 0 ≤ B := sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt (4 * B + 2 + 2 * |hNeed (parEps k r)|)
  refine ⟨t₀, fun t ht => ?_⟩
  have htR : 4 * B + 2 + 2 * |hNeed (parEps k r)| < (t : ℝ) :=
    lt_of_lt_of_le ht₀ (by exact_mod_cast ht)
  have hNa := le_abs_self (hNeed (parEps k r))
  have hNb := abs_nonneg (hNeed (parEps k r))
  have key : ∀ a c : Fin (2 * r + k + 1), a.val + 1 - k < c.val + 1 - k →
      (t : ℝ) / 2 ≤ lamT k r u b t a - lamT k r u b t c := by
    intro a c hac
    rw [lamT_eq_sub k r hk u b t a, lamT_eq_sub k r hk u b t c]
    have h1 : ((a.val + 1 - k : ℕ) : ℝ) + 1 ≤ ((c.val + 1 - k : ℕ) : ℝ) := by exact_mod_cast hac
    have h2 := abs_le.1 (hBa a)
    have h3 := abs_le.1 (hBa c)
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith [mul_le_mul_of_nonneg_right h1 ht0]
  have hanti : StrictAnti (lamT k r u b t) := by
    intro a c hac
    have hac' : a.val < c.val := hac
    by_cases hc : c.val < k
    · have ha : a.val < k := by omega
      have hu := u_strictAnti k r u v b hI (show (⟨a.val, ha⟩ : Fin k) < ⟨c.val, hc⟩ from hac')
      simp only [lamT, ha, hc, ↓reduceDIte]
      linarith
    · have := key a c (by omega)
      linarith
  refine ⟨⟨hanti, fun a => ?_⟩, hanti, ?_, ?_⟩
  · by_cases ha : a.val < k
    · obtain ⟨m1, hm1⟩ := hH ⟨a.val, ha⟩ a
      obtain ⟨m2, hm2⟩ := hP.2 a
      refine ⟨m1 + m2, ?_⟩
      simp only [lamT, ha, ↓reduceDIte]
      push_cast at hm2 ⊢
      linarith
    · obtain ⟨m2, hm2⟩ := hP.2 a
      refine ⟨m2 - ((a.val + 1 - k : ℕ) : ℤ) * (t : ℤ), ?_⟩
      rw [lamT_eq_parLam k r hk u v b t a (by omega)]
      push_cast at hm2 ⊢
      linarith
  · intro a c hne
    have hj : a.val + 1 - k ≠ c.val + 1 - k := by
      intro h
      apply hne
      by_cases ha : a.val < k
      · have hc : c.val < k := by omega
        rw [parEps_true_of_lt k r hk a ha, parEps_true_of_lt k r hk c hc]
      · have : a = c := Fin.ext (by omega)
        rw [this]
    rcases lt_or_gt_of_ne hj with h | h
    · exact le_trans (key a c h) (le_abs_self _)
    · rw [abs_sub_comm]
      exact le_trans (key c a h) (le_abs_self _)
  · linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
