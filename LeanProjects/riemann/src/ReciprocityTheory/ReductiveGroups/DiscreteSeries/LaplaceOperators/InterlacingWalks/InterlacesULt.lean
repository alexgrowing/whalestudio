import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.AdjGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.Imports

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

noncomputable def lowPt (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (i : ℕ) (x : ℝ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun a => if a.val = i then x else walkPar k r u v b (i + 1) a

theorem interlaces_u_lt {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) :
    ∀ (j d : ℕ) (h1 : j + d + 1 < k), u ⟨j + d + 1, h1⟩ < u ⟨j, by omega⟩ := by
  intro j d
  induction d with
  | zero =>
    intro h1
    have hj : j < k - 1 := by omega
    have h2 := hI.1 ⟨j, hj⟩
    exact lt_trans h2.2 h2.1
  | succ d ih =>
    intro h1
    have hj : j + d + 1 < k - 1 := by omega
    have h2 := hI.1 ⟨j + d + 1, hj⟩
    have h3 := ih (by omega)
    exact lt_trans (lt_trans h2.2 h2.1) h3

theorem u_lt {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) (j l : Fin k) (hjl : j.val < l.val) : u l < u j := by
  obtain ⟨j, hj⟩ := j
  obtain ⟨l, hl⟩ := l
  have hjl' : j < l := hjl
  obtain ⟨d, rfl⟩ : ∃ d, l = j + d + 1 := ⟨l - j - 1, by omega⟩
  exact interlaces_u_lt hI j d hl

theorem u_lt_v {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) (i : ℕ) (hi : i < k - 1) (j : Fin k) (hij : i < j.val) :
    u j < v ⟨i, hi⟩ := by
  have h := (hI.1 ⟨i, hi⟩).2
  rcases Nat.lt_or_ge (i + 1) j.val with h1 | h1
  · exact lt_trans (u_lt hI ⟨i + 1, by omega⟩ j h1) h
  · have hj : j = ⟨i + 1, by omega⟩ := Fin.ext (show j.val = i + 1 by omega)
    rw [hj]
    exact h

theorem parLam_of_lt {k r : ℕ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (a : ℕ)
    (ha : a < 2 * r + k + 1) (h : a < k - 1) : parLam k r v b ⟨a, ha⟩ = v ⟨a, h⟩ := by
  simp [parLam, h]

theorem parLam_of_ge {k r : ℕ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (a : ℕ)
    (ha : a < 2 * r + k + 1) (h : k - 1 ≤ a) :
    parLam k r v b ⟨a, ha⟩ = -b ⟨a - (k - 1), by omega⟩ := by
  have h' : ¬ a < k - 1 := by omega
  simp [parLam, h']

theorem lam_lt_u {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) :
    parLam k r v b ⟨i, hin⟩ < u ⟨i, hi⟩ := by
  rcases Nat.lt_or_ge i (k - 1) with h | h
  · rw [parLam_of_lt i hin h]
    exact (hI.1 ⟨i, h⟩).1
  · obtain rfl : i = k - 1 := by omega
    rw [parLam_of_ge (k - 1) hin h]
    have h2 := hI.2 (by omega)
    have e : b ⟨k - 1 - (k - 1), by omega⟩ = b ⟨0, by omega⟩ :=
      congrArg b (Fin.ext (show k - 1 - (k - 1) = 0 by omega))
    rw [e]
    exact h2

theorem lam_gap {k r : ℕ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} {h : ℝ} (hk : 1 ≤ k)
    (hG : LowGaps r b h) (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hka : k - 1 ≤ a.val) :
    h ≤ parLam k r v b a - parLam k r v b ⟨a.val + 1, ha⟩ := by
  have haa := a.isLt
  have hj : a.val - (k - 1) + 1 < 2 * r + 2 := by omega
  have h1 : parLam k r v b a = -b ⟨a.val - (k - 1), by omega⟩ := parLam_of_ge a.val a.isLt hka
  have hg : h ≤ b ⟨a.val - (k - 1) + 1, hj⟩ - b ⟨a.val - (k - 1), by omega⟩ :=
    hG ⟨a.val - (k - 1), by omega⟩ hj
  have e : (⟨a.val - (k - 1) + 1, hj⟩ : Fin (2 * r + 2)) = ⟨a.val + 1 - (k - 1), by omega⟩ :=
    Fin.ext (show a.val - (k - 1) + 1 = a.val + 1 - (k - 1) by omega)
  rw [e] at hg
  rw [h1, parLam_of_ge (a.val + 1) ha (by omega)]
  linarith

theorem parEps_adj {k r : ℕ} (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hne : parEps k r a ≠ parEps k r ⟨a.val + 1, ha⟩) : k - 1 ≤ a.val := by
  by_contra hlt
  have h1 : a.val < k - 1 := by omega
  have hl : parEps k r a = true := by
    show (if a.val < k - 1 then true else decide ((a.val - (k - 1)) % 2 = 0)) = true
    rw [if_pos h1]
  have hr : parEps k r ⟨a.val + 1, ha⟩ = true := by
    show (if a.val + 1 < k - 1 then true else decide ((a.val + 1 - (k - 1)) % 2 = 0)) = true
    split
    · rfl
    · rw [show a.val + 1 - (k - 1) = 0 by omega]
      rfl
  exact hne (hl.trans hr.symm)

theorem lowPt_at {k r : ℕ} (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : ℕ) (x : ℝ) (hin : i < 2 * r + k + 1) : lowPt k r u v b i x ⟨i, hin⟩ = x := by
  show (if i = i then x else walkPar k r u v b (i + 1) ⟨i, hin⟩) = x
  rw [if_pos rfl]

theorem lowPt_lt {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (i : ℕ) (x : ℝ) (hi : i < k) (a : Fin (2 * r + k + 1)) (ha : a.val < i) :
    lowPt k r u v b i x a = u ⟨a.val, by omega⟩ - 1 / 2 := by
  have h1 : a.val ≠ i := by omega
  have h2 : a.val < i + 1 ∧ a.val < k := ⟨by omega, by omega⟩
  show (if a.val = i then x else walkPar k r u v b (i + 1) a) = _
  rw [if_neg h1]
  show (if h : a.val < i + 1 ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a) = _
  rw [dif_pos h2]

theorem lowPt_gt {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (i : ℕ) (x : ℝ) (a : Fin (2 * r + k + 1)) (ha : i < a.val) :
    lowPt k r u v b i x a = parLam k r v b a := by
  have h1 : a.val ≠ i := by omega
  have h2 : ¬ (a.val < i + 1 ∧ a.val < k) := fun h' => absurd h'.1 (by omega)
  show (if a.val = i then x else walkPar k r u v b (i + 1) a) = _
  rw [if_neg h1]
  show (if h : a.val < i + 1 ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a) = _
  rw [dif_neg h2]

theorem walkPar_add {k r : ℕ} (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) (c : ℝ) :
    walkPar k r u v b (i + 1) + c • Pi.single (⟨i, hin⟩ : Fin (2 * r + k + 1)) (1 : ℝ) =
      lowPt k r u v b i (u ⟨i, hi⟩ - 1 / 2 + c) := by
  funext a
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases ha : a.val = i
  · obtain rfl : a = ⟨i, hin⟩ := Fin.ext ha
    rw [lowPt_at, Pi.single_eq_same, mul_one]
    have h2 : i < i + 1 ∧ i < k := ⟨Nat.lt_succ_self i, hi⟩
    show (if h : i < i + 1 ∧ i < k then u ⟨i, h.2⟩ - 1 / 2 else parLam k r v b ⟨i, hin⟩) + c = _
    rw [dif_pos h2]
  · have hne : a ≠ ⟨i, hin⟩ := fun h => ha (congrArg Fin.val h)
    rw [Pi.single_apply, if_neg hne, mul_zero, add_zero]
    show _ = (if a.val = i then _ else walkPar k r u v b (i + 1) a)
    rw [if_neg ha]

theorem lowPt_sub {k r : ℕ} (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : ℕ) (hin : i < 2 * r + k + 1) (y : ℝ) :
    lowPt k r u v b i y - Pi.single (⟨i, hin⟩ : Fin (2 * r + k + 1)) (1 : ℝ) =
      lowPt k r u v b i (y - 1) := by
  funext a
  rw [Pi.sub_apply]
  by_cases ha : a.val = i
  · obtain rfl : a = ⟨i, hin⟩ := Fin.ext ha
    rw [lowPt_at, lowPt_at, Pi.single_eq_same]
  · have hne : a ≠ ⟨i, hin⟩ := fun h => ha (congrArg Fin.val h)
    rw [Pi.single_apply, if_neg hne, sub_zero]
    show (if a.val = i then y else walkPar k r u v b (i + 1) a) =
      (if a.val = i then y - 1 else walkPar k r u v b (i + 1) a)
    rw [if_neg ha, if_neg ha]

theorem lowPt_bot {k r : ℕ} (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) :
    lowPt k r u v b i (parLam k r v b ⟨i, hin⟩) = walkPar k r u v b i := by
  funext a
  rcases lt_trichotomy a.val i with h | h | h
  · rw [lowPt_lt (u := u) (v := v) (b := b) i (parLam k r v b ⟨i, hin⟩) hi a h]
    have h2 : a.val < i ∧ a.val < k := ⟨h, by omega⟩
    show _ = (if h : a.val < i ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a)
    rw [dif_pos h2]
  · obtain rfl : a = ⟨i, hin⟩ := Fin.ext h
    rw [lowPt_at]
    have h2 : ¬ (i < i ∧ i < k) := fun h' => lt_irrefl i h'.1
    show _ = (if h : i < i ∧ i < k then u ⟨i, h.2⟩ - 1 / 2 else parLam k r v b ⟨i, hin⟩)
    rw [dif_neg h2]
  · rw [lowPt_gt (u := u) (v := v) (b := b) i (parLam k r v b ⟨i, hin⟩) a h]
    have h2 : ¬ (a.val < i ∧ a.val < k) := fun h' => absurd h'.1 (by omega)
    show _ = (if h : a.val < i ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a)
    rw [dif_neg h2]

private theorem gapAtLeast_of_adjacent_sign_change_ge {n : ℕ} (ε : Fin n → Bool) (L : Fin n → ℝ) (h : ℝ)
    (hL : StrictAnti L)
    (hadj : ∀ a c : Fin n, c.val = a.val + 1 → ε a ≠ ε c → h ≤ L a - L c) :
    GapAtLeast ε L h := by
  have key : ∀ (d : ℕ) (a c : Fin n), c.val = a.val + d + 1 → ε a ≠ ε c → h ≤ L a - L c := by
    intro d
    induction d with
    | zero =>
      intro a c hac hne
      exact hadj a c (by omega) hne
    | succ d ih =>
      intro a c hac hne
      have hm : a.val + 1 < n := by have := c.isLt; omega
      obtain ⟨m, hmv⟩ : ∃ m : Fin n, m.val = a.val + 1 := ⟨⟨a.val + 1, hm⟩, rfl⟩
      have ham : a < m := Fin.lt_def.mpr (by omega)
      have hmc : m < c := Fin.lt_def.mpr (by omega)
      have h1 : L m < L a := hL ham
      have h2 : L c < L m := hL hmc
      by_cases hε : ε a = ε m
      · have h3 := ih m c (by omega) (fun heq => hne (hε.trans heq))
        linarith
      · have h3 := hadj a m hmv hε
        linarith
  intro a c hne
  rcases lt_trichotomy a.val c.val with hac | hac | hac
  · have h1 := key (c.val - a.val - 1) a c (by omega) hne
    have h2 : L c < L a := hL (Fin.lt_def.mpr hac)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ L a - L c by linarith)]
    exact h1
  · exact absurd (congrArg ε (Fin.ext hac)) hne
  · have h1 := key (a.val - c.val - 1) c a (by omega) (Ne.symm hne)
    have h2 : L a < L c := hL (Fin.lt_def.mpr hac)
    rw [abs_of_neg (show L a - L c < 0 by linarith)]
    linarith

theorem lowPt_ok {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} {h : ℝ}
    (hk : 1 ≤ k) (hHC : IsHCPar (parLam k r v b)) (hI : Interlaces k r u v b)
    (hH : HalfInts k r u v b) (hG : LowGaps r b h) (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1)
    (x : ℝ) (m : ℤ) (hx : x = parLam k r v b ⟨i, hin⟩ + m) (hlo : parLam k r v b ⟨i, hin⟩ ≤ x)
    (hhi : x ≤ u ⟨i, hi⟩ - 1 / 2) :
    IsHCPar (lowPt k r u v b i x) ∧ GapAtLeast (parEps k r) (lowPt k r u v b i x) h := by
  obtain ⟨hanti0, hint0⟩ := hHC
  have hLlt : ∀ (a : Fin (2 * r + k + 1)) (ha : a.val < i),
      lowPt k r u v b i x a = u ⟨a.val, by omega⟩ - 1 / 2 :=
    fun a ha => lowPt_lt i x hi a ha
  have hLgt : ∀ (a : Fin (2 * r + k + 1)), i < a.val → lowPt k r u v b i x a = parLam k r v b a :=
    fun a ha => lowPt_gt i x a ha
  have hLeq : ∀ (a : Fin (2 * r + k + 1)), a.val = i → lowPt k r u v b i x a = x := by
    intro a ha
    obtain rfl : a = ⟨i, hin⟩ := Fin.ext ha
    exact lowPt_at u v b i x hin
  have hu : ∀ (a : Fin (2 * r + k + 1)) (ha : a.val < i), u ⟨i, hi⟩ < u ⟨a.val, by omega⟩ :=
    fun a ha => u_lt hI ⟨a.val, by omega⟩ ⟨i, hi⟩ ha
  have hP : ∀ c : Fin (2 * r + k + 1), i < c.val → parLam k r v b c < parLam k r v b ⟨i, hin⟩ :=
    fun c hc => hanti0 (show (⟨i, hin⟩ : Fin (2 * r + k + 1)) < c from Fin.lt_def.mpr hc)
  have hanti : StrictAnti (lowPt k r u v b i x) := by
    intro a c hac
    have hac' : a.val < c.val := Fin.lt_def.mp hac
    rcases lt_trichotomy c.val i with hc | hc | hc
    · have ha : a.val < i := by omega
      rw [hLlt a ha, hLlt c hc]
      have h1 := u_lt hI ⟨a.val, by omega⟩ ⟨c.val, by omega⟩ hac'
      linarith
    · have ha : a.val < i := by omega
      rw [hLlt a ha, hLeq c hc]
      have h1 := hu a ha
      linarith
    · rw [hLgt c hc]
      have h1 := hP c hc
      rcases lt_trichotomy a.val i with ha | ha | ha
      · rw [hLlt a ha]
        have h2 := hu a ha
        linarith
      · rw [hLeq a ha]
        linarith
      · rw [hLgt a ha]
        exact hanti0 hac
  have hint : ∀ a : Fin (2 * r + k + 1),
      ∃ m : ℤ, lowPt k r u v b i x a - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ) := by
    intro a
    obtain ⟨m0, hm0⟩ := hint0 a
    rcases lt_trichotomy a.val i with ha | ha | ha
    · obtain ⟨m1, hm1⟩ := hH ⟨a.val, by omega⟩ a
      refine ⟨m0 + m1, ?_⟩
      rw [hLlt a ha, Int.cast_add]
      linarith
    · obtain ⟨m1, hm1⟩ := hint0 ⟨i, hin⟩
      refine ⟨m1 + m, ?_⟩
      rw [hLeq a ha, hx, Int.cast_add]
      linarith
    · rw [hLgt a ha]
      exact ⟨m0, hm0⟩
  have hadj : ∀ a c : Fin (2 * r + k + 1), c.val = a.val + 1 → parEps k r a ≠ parEps k r c →
      h ≤ lowPt k r u v b i x a - lowPt k r u v b i x c := by
    intro a c hcv hne
    have hc : a.val + 1 < 2 * r + k + 1 := by have := c.isLt; omega
    have hcE : c = ⟨a.val + 1, hc⟩ := Fin.ext hcv
    rw [hcE] at hne ⊢
    have hka := parEps_adj a hc hne
    have hg := lam_gap (v := v) hk hG a hc hka
    rw [hLgt ⟨a.val + 1, hc⟩ (show i < a.val + 1 by omega)]
    rcases lt_or_eq_of_le (show i ≤ a.val by omega) with ha | ha
    · rw [hLgt a ha]
      exact hg
    · rw [hLeq a ha.symm]
      have haE : a = ⟨i, hin⟩ := Fin.ext ha.symm
      have hPa : parLam k r v b a = parLam k r v b ⟨i, hin⟩ := by rw [haE]
      linarith
  exact ⟨And.intro hanti hint, gapAtLeast_of_adjacent_sign_change_ge _ _ _ hanti hadj⟩

theorem no_cross {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) (y : ℝ)
    (h1 : parLam k r v b ⟨i, hin⟩ + 1 ≤ y) (h2 : y ≤ u ⟨i, hi⟩ - 1 / 2) (l : Fin k) :
    u l ≠ y - 1 / 2 := by
  intro heq
  rcases lt_trichotomy l.val i with hl | hl | hl
  · have h3 := u_lt hI l ⟨i, hi⟩ hl
    linarith
  · have hl' : l = ⟨i, hi⟩ := Fin.ext hl
    subst hl'
    linarith
  · have hik : i < k - 1 := by have := l.isLt; omega
    have h3 := u_lt_v hI i hik l hl
    rw [parLam_of_lt i hin hik] at h1
    linarith

theorem lowerStep : LowerStepStatement := by
  unfold LowerStepStatement
  intro k r u v b h P hk hHC hI hH hG hSC i hi hP
  have hin : i < 2 * r + k + 1 := by omega
  have e1 : walkPar k r u v b (i + 1) = lowPt k r u v b i (u ⟨i, hi⟩ - 1 / 2) := by
    have h0 := walkPar_add u v b i hi hin 0
    rw [zero_smul, add_zero, add_zero] at h0
    exact h0
  rw [← lowPt_bot u v b i hi hin]
  obtain ⟨m, hm⟩ := hH ⟨i, hi⟩ ⟨i, hin⟩
  have hlt := lam_lt_u hI i hi hin
  have hm0 : 0 ≤ m := by
    by_contra hneg
    have h1 : m ≤ -1 := by omega
    have h2 : (m : ℝ) ≤ -1 := by exact_mod_cast h1
    linarith
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, m = N := ⟨m.toNat, (Int.toNat_of_nonneg hm0).symm⟩
  have hm' : u ⟨i, hi⟩ - parLam k r v b ⟨i, hin⟩ = (N : ℝ) + 1 / 2 := by exact_mod_cast hm
  have ok : ∀ t : ℕ, t ≤ N →
      IsHCPar (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + (t : ℝ))) ∧
      GapAtLeast (parEps k r) (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + (t : ℝ))) h := by
    intro t ht
    have htN : (t : ℝ) ≤ N := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    exact lowPt_ok hk hHC hI hH hG i hi hin _ (t : ℤ) (by simp) (by linarith) (by linarith)
  have key : ∀ t : ℕ, t ≤ N → P (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + (t : ℝ))) →
      P (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩)) := by
    intro t
    induction t with
    | zero =>
      intro _ hp
      simpa using hp
    | succ t ih =>
      intro ht hp
      apply ih (by omega)
      have hy := ok (t + 1) ht
      have hy' := ok t (by omega)
      have hsub := lowPt_sub u v b i hin (parLam k r v b ⟨i, hin⟩ + ((t + 1 : ℕ) : ℝ))
      have e : parLam k r v b ⟨i, hin⟩ + ((t + 1 : ℕ) : ℝ) - 1 =
          parLam k r v b ⟨i, hin⟩ + (t : ℝ) := by
        rw [Nat.cast_succ]
        ring
      rw [e] at hsub
      have hnc : ∀ l, u l ≠
          lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + ((t + 1 : ℕ) : ℝ)) ⟨i, hin⟩ - 1 / 2 := by
        intro l
        rw [lowPt_at]
        have htN : ((t + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast ht
        have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
        have hc : ((t + 1 : ℕ) : ℝ) = t + 1 := Nat.cast_succ t
        exact no_cross hI i hi hin _ (by linarith) (by linarith) l
      have h3 := hSC.1 _ ⟨i, hin⟩ hy.1 hy.2 (by rw [hsub]; exact hy'.1) (by rw [hsub]; exact hy'.2)
        hnc hp
      rw [hsub] at h3
      exact h3
  have e2 : parLam k r v b ⟨i, hin⟩ + ((N : ℕ) : ℝ) = u ⟨i, hi⟩ - 1 / 2 := by linarith
  apply key N le_rfl
  rw [e2, ← e1]
  exact hP

end ReciprocityTheory.ChartRestriction.DS.Lap
