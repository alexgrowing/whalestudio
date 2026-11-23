import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem sum_shift_le : ∀ (K : ℕ) [NeZero K] (f g : Fin K → ℤ), (∀ c, 0 ≤ g c) →
    (∀ (c : Fin K) (h : c.val + 1 < K), f ⟨c.val + 1, h⟩ ≤ g c) → ∑ c, f c ≤ f 0 + ∑ c, g c := by
  intro K
  cases K with
  | zero => intro h; exact absurd rfl (NeZero.ne (0 : ℕ))
  | succ K =>
    intro _ f g hg hfg
    rw [Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
    have h1 : ∑ c : Fin K, f c.succ ≤ ∑ c : Fin K, g c.castSucc :=
      Finset.sum_le_sum fun c _ => hfg c.castSucc (by simp)
    have h2 := hg (Fin.last K)
    linarith

theorem int_pos_neg (x : ℤ) : x = max x 0 - max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

variable {N r K : ℕ}

theorem posS_split (la : Fin (r + K) → ℤ) :
    posS la = ∑ c : Fin r, max (la (Fin.castAdd K c)) 0 + ∑ c : Fin K, max (la (Fin.natAdd r c)) 0 := by
  unfold posS; rw [Fin.sum_univ_add]

theorem negS_split (la : Fin (r + K) → ℤ) :
    negS la = ∑ c : Fin r, max (-la (Fin.castAdd K c)) 0 + ∑ c : Fin K, max (-la (Fin.natAdd r c)) 0 := by
  unfold negS; rw [Fin.sum_univ_add]

theorem dplus_le_geom {LL : Letters (Fin N)} {B : Fin N → ℕ} {n0 p : ℕ} (hp : 13 ≤ p)
    (H2 : ∀ i i' : Fin N, i < i' → i'.val < n0 → LL.vec i = LL.vec i' → (p : ℝ) ^ 2 / 5 * (B i : ℝ) ≤ (B i' : ℝ)) :
    ∀ (m : ℕ) (l : Fin N), LL.vec l = true → m ≤ l.val → l.val < n0 →
      (dplus LL B m : ℝ) ≤ 10 / (p : ℝ) ^ 2 * (B l : ℝ) := by
  have hp' : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  intro m
  induction m with
  | zero =>
    intro l _ _ _
    have : dplus LL B 0 = 0 := by unfold dplus; simp
    rw [this]; push_cast; positivity
  | succ m ih =>
    intro l hl hml hln
    have hmN : m < N := by have := l.2; omega
    have hd : dplus LL B (m + 1) = dplus LL B m + if LL.vec ⟨m, hmN⟩ = true then B ⟨m, hmN⟩ else 0 :=
      dsum_succ (fun l => LL.vec l = true) B m hmN
    rw [hd]
    by_cases hv : LL.vec ⟨m, hmN⟩ = true
    · rw [if_pos hv]
      have h1 := ih ⟨m, hmN⟩ hv le_rfl (by simp only; omega)
      have h2 := H2 ⟨m, hmN⟩ l (by rw [Fin.lt_def]; simp only; omega) hln (by rw [hv, hl])
      push_cast
      have hB : (0 : ℝ) ≤ (B ⟨m, hmN⟩ : ℝ) := Nat.cast_nonneg _
      have h3 : (B ⟨m, hmN⟩ : ℝ) ≤ 5 / (p : ℝ) ^ 2 * (B l : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : (p : ℝ) ^ 2 / 5 * (B ⟨m, hmN⟩ : ℝ) = (B ⟨m, hmN⟩ : ℝ) * (p : ℝ) ^ 2 / 5 := by ring
        rw [this, div_le_iff₀ (by norm_num)] at h2
        linarith
      have h4 : 10 / (p : ℝ) ^ 2 ≤ 10 / 169 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
      have h5 : 10 / (p : ℝ) ^ 2 * (B ⟨m, hmN⟩ : ℝ) ≤ 10 / 169 * (B ⟨m, hmN⟩ : ℝ) :=
        mul_le_mul_of_nonneg_right h4 hB
      have h6 : 10 / (p : ℝ) ^ 2 * (B l : ℝ) = 2 * (5 / (p : ℝ) ^ 2 * (B l : ℝ)) := by ring
      rw [h6]
      linarith
    · rw [if_neg hv]
      simpa using ih l hl (by omega) hln

theorem oldest_lt_n0 {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}
    (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) : (od i).val < n0 := by
  by_contra hcon
  have h1 := H.od_card i hi
  have h2 : (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true).card ≤
      (Finset.Ico (od i) i).card := by
    refine Finset.card_le_card ?_
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact Finset.mem_Ico.mpr ⟨hl.1, hl.2.1⟩
  rw [Fin.card_Ico] at h2
  have := i.2
  have := H.hN
  omega

theorem vcount_od {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}
    (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) :
    vcount LL ((od i).val + 1) i.val + 1 = r := by
  classical
  have h1 := H.od_card i hi
  have h2 : (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true) =
      insert (od i) (Finset.univ.filter fun l : Fin N => (od i).val + 1 ≤ l.val ∧ l.val < i.val ∧ LL.vec l = true) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hl : l = od i
      · exact Or.inl hl
      · refine Or.inr ⟨?_, h2, h3⟩
        have : (od i).val ≠ l.val := fun h => hl (Fin.ext h.symm)
        have h1' : (od i).val ≤ l.val := h1
        omega
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨le_rfl, H.od_lt i hi, H.od_vec i hi⟩
      · exact ⟨by rw [Fin.le_def]; omega, h2, h3⟩
  rw [h2, Finset.card_insert_of_notMem (by simp)] at h1
  exact h1

theorem nu_last_le [NeZero r] {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ}
    {a La : ℝ} {p : ℕ} (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (i : Fin N) (hi : r ≤ i.val) :
    ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) ≤ 2 * (B (od i) : ℝ) := by
  have hr := H.r1
  have hod := oldest_lt_n0 H i hi
  have hvc := vcount_od H i hi
  have hlt : (od i).val < i.val := H.od_lt i hi
  have h1 := row_back P ((od i).val + 1) i.val (by omega) (by have := i.2; omega) ⟨0, by omega⟩
    (Fin.castAdd K (lastIdx r)) (by simp [lastIdx]; omega)
  have h2 := mu_le_dplus P ((od i).val + 1) (by have := i.2; omega) ⟨0, by omega⟩
  have h3 : dplus LL dd ((od i).val + 1) = dplus LL B ((od i).val + 1) := by
    unfold dplus
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.val < (od i).val + 1 ∧ LL.vec l = true
    · rw [if_pos hl, if_pos hl, hdd l (by omega)]
    · rw [if_neg hl, if_neg hl]
  have h4 : dplus LL B ((od i).val + 1) = dplus LL B (od i).val + B (od i) := by
    have := dsum_succ (fun l => LL.vec l = true) B (od i).val (od i).2
    rw [if_pos (H.od_vec i hi)] at this
    exact this
  have h5 := dplus_le_geom H.p13 H.H2 (od i).val (od i) (H.od_vec i hi) le_rfl hod
  have hp' : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast H.p13
  have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have h6 : 10 / (p : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hB : (0 : ℝ) ≤ (B (od i) : ℝ) := Nat.cast_nonneg _
  have h7 : (plPart P.mu i.castSucc (lastIdx r) : ℤ) ≤ (dplus LL dd ((od i).val + 1) : ℤ) := le_trans h1 h2
  have h8 : ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) ≤ ((dplus LL dd ((od i).val + 1) : ℕ) : ℝ) := by
    exact_mod_cast h7
  rw [h3, h4] at h8
  push_cast at h8
  have h9 : 10 / (p : ℝ) ^ 2 * (B (od i) : ℝ) ≤ 1 * (B (od i) : ℝ) := mul_le_mul_of_nonneg_right h6 hB
  linarith

theorem typical_path_orders_small : TypicalPathOrdersSmall := by
  intro N n0 r K _ _ LL B od bb a La p H μ hμ hTyp i hi
  obtain ⟨dd, hP⟩ := hμ
  obtain ⟨P, rfl⟩ := hP.path
  have hr := H.r1
  have hK := H.N_add_r_le_K
  have F1 : ∀ (s : Fin (N + 1)) (m : Fin (r + K)), m.val ≤ r → 0 ≤ P.mu s m := by
    intro s m hm
    exact mu_nonneg P s.val s.2 m (by have := s.2; omega)
  obtain ⟨hT1, hT2, hT3⟩ := hTyp i
  refine ⟨hT3 hi, ?_, ?_⟩
  · intro hv
    have hstep := step_vec P i hv
    have hX := hT2 hv hi

    have hneg : ∀ s : Fin (N + 1), negS (P.mu s) = ∑ c : Fin K, max (-tanPart P.mu s c) 0 := by
      intro s
      rw [negS_split]
      have : ∑ c : Fin r, max (-P.mu s (Fin.castAdd K c)) 0 = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        have := F1 s (Fin.castAdd K c) (by simp)
        exact max_eq_right (by linarith)
      rw [this, zero_add]; rfl
    have hshift : ∑ c : Fin K, max (tanPart P.mu i.succ c) 0 ≤
        max (tanPart P.mu i.succ 0) 0 + ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0 := by
      refine sum_shift_le K (fun c => max (tanPart P.mu i.succ c) 0) (fun c => max (tanPart P.mu i.castSucc c) 0)
        (fun c => le_max_right _ _) ?_
      intro c h
      refine max_le_max ?_ le_rfl
      have := hstep.2.1 (Fin.natAdd r c) (by simp; omega)
      exact this
    have hfirst : tanPart P.mu i.succ 0 ≤ plPart P.mu i.castSucc (lastIdx r) := by
      have := hstep.2.1 (Fin.castAdd K (lastIdx r)) (by simp [lastIdx]; omega)
      have he : (⟨(Fin.castAdd K (lastIdx r)).val + 1, by simp [lastIdx]; omega⟩ : Fin (r + K)) =
          Fin.natAdd r (0 : Fin K) := by
        apply Fin.ext; simp [lastIdx]; omega
      rw [he] at this
      exact this
    have hnn : 0 ≤ plPart P.mu i.castSucc (lastIdx r) := F1 _ _ (by simp [lastIdx])
    have hsum : ∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) =
        (∑ c : Fin K, max (tanPart P.mu i.succ c) 0 - ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0) +
        (negS (P.mu i.castSucc) - negS (P.mu i.succ)) := by
      rw [hneg, hneg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 := int_pos_neg (tanPart P.mu i.succ c)
      have h2 := int_pos_neg (tanPart P.mu i.castSucc c)
      linarith
    have hle : ∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) ≤
        plPart P.mu i.castSucc (lastIdx r) + (negS (P.mu i.castSucc) - negS (P.mu i.succ)) := by
      rw [hsum]
      have : max (tanPart P.mu i.succ 0) 0 ≤ plPart P.mu i.castSucc (lastIdx r) := max_le hfirst hnn
      linarith
    have hle' : ((∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) : ℤ) : ℝ) ≤
        ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) + ((negS (P.mu i.castSucc) - negS (P.mu i.succ) : ℤ) : ℝ) := by
      exact_mod_cast hle
    have hnu := nu_last_le H P hP.degs i hi
    linarith
  · intro hv
    have hstep := step_cov P i hv
    have hX := hT1 hv
    have hpos : ∀ s : Fin (N + 1), posS (P.mu s) = ∑ c : Fin r, plPart P.mu s c +
        ∑ c : Fin K, max (tanPart P.mu s c) 0 := by
      intro s
      rw [posS_split]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      exact max_eq_left (F1 s (Fin.castAdd K c) (by simp))
    have hmono : ∑ c : Fin K, max (tanPart P.mu i.succ c) 0 ≤ ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0 :=
      Finset.sum_le_sum fun c _ => max_le_max (hstep.1 (Fin.natAdd r c)) le_rfl
    have hle : ∑ c, (plPart P.mu i.castSucc c - plPart P.mu i.succ c) ≤
        posS (P.mu i.castSucc) - posS (P.mu i.succ) := by
      rw [hpos, hpos, Finset.sum_sub_distrib]
      linarith
    have hle' : ((∑ c, (plPart P.mu i.castSucc c - plPart P.mu i.succ c) : ℤ) : ℝ) ≤
        ((posS (P.mu i.castSucc) - posS (P.mu i.succ) : ℤ) : ℝ) := by exact_mod_cast hle
    linarith

end Formalism.MainNotions.SelectionLemmas.Pf.T
