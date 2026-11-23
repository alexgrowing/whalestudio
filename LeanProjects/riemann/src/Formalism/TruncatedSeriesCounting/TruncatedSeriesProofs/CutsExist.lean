import Formalism.TruncatedSeriesCounting.PowMemSpanOfMemSpanLinearDistinguished

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

namespace ClusterCuts

variable (j : ℕ) (th : ℤ → Prop) [DecidablePred th]

def Step (x y : ℤ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ j → ¬ th (x + i)) ∧ (j : ℤ) ≤ y - x ∧ y - x ≤ 3 * j + 1 ∧
    ((Finset.Ioc x y).filter th).card ≤ 2

def Chain (a b : ℤ) : Prop :=
  ∃ (m : ℕ) (c : ℕ → ℤ), 1 ≤ m ∧ c 0 = a ∧ c m = b ∧ ∀ k < m, Step j th (c k) (c (k + 1))

def ClustersZ : Prop :=
  ∀ t : ℤ, th t → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k))

variable {j th}

lemma chain_of_step {a b : ℤ} (h : Step j th a b) : Chain j th a b := by
  refine ⟨1, fun k => if k = 0 then a else b, le_rfl, by simp, by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simpa using h

lemma chain_trans {a b d : ℤ} (h1 : Chain j th a b) (h2 : Chain j th b d) :
    Chain j th a d := by
  obtain ⟨m1, c1, hm1, h10, h1m, hs1⟩ := h1
  obtain ⟨m2, c2, hm2, h20, h2m, hs2⟩ := h2
  refine ⟨m1 + m2, fun k => if k ≤ m1 then c1 k else c2 (k - m1), by omega, ?_, ?_, ?_⟩
  · simp [h10]
  · have hn : ¬ (m1 + m2 ≤ m1) := by omega
    simp only [hn, if_false]
    rw [Nat.add_sub_cancel_left]
    exact h2m
  · intro k hk
    by_cases hk1 : k + 1 ≤ m1
    · have hk0 : k ≤ m1 := by omega
      simp only [hk0, hk1, if_true]
      exact hs1 k (by omega)
    · by_cases hkm : k = m1
      · subst hkm
        simp only [le_refl, if_true, hk1, if_false]
        rw [h1m, ← h20, show k + 1 - k = 0 + 1 by omega]
        exact hs2 0 hm2
      · have hk0 : ¬ k ≤ m1 := by omega
        simp only [hk0, hk1, if_false]
        rw [show k + 1 - m1 = (k - m1) + 1 by omega]
        exact hs2 (k - m1) (by omega)

lemma fill (hj : 1 ≤ j) (s : ℕ) : ∀ (a e : ℤ), j ≤ s →
    (∀ i : ℤ, a < i → i ≤ a + s → ¬ th i) → a + s ≤ e → e ≤ a + s + j + 1 →
    ((Finset.Ioc (a + s) e).filter th).card ≤ 2 → Chain j th a e := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a e hs hfree hae hea hcard
    by_cases h2 : s < 2 * j
    · apply chain_of_step
      refine ⟨?_, by omega, by omega, ?_⟩
      · intro i hi1 hij
        apply hfree <;> omega
      · calc ((Finset.Ioc a e).filter th).card
            ≤ ((Finset.Ioc (a + s) e).filter th).card := by
              apply Finset.card_le_card
              intro i hi
              simp only [Finset.mem_filter, Finset.mem_Ioc] at hi ⊢
              refine ⟨⟨?_, hi.1.2⟩, hi.2⟩
              by_contra hc
              push Not at hc
              exact hfree i hi.1.1 hc hi.2
          _ ≤ 2 := hcard
    · push Not at h2
      apply chain_trans (b := a + j)
      · apply chain_of_step
        refine ⟨?_, by omega, by omega, ?_⟩
        · intro i hi1 hij
          apply hfree <;> omega
        · have he : (Finset.Ioc a (a + j)).filter th = ∅ := by
            apply Finset.filter_false_of_mem
            intro i hi
            simp only [Finset.mem_Ioc] at hi
            exact hfree i hi.1 (by omega)
          rw [he]
          simp
      · have hsj : ((s - j : ℕ) : ℤ) = (s : ℤ) - j := by
          rw [Nat.cast_sub (by omega)]
        have hpt : a + (j : ℤ) + ((s - j : ℕ) : ℤ) = a + s := by rw [hsj]; ring
        apply ih (s - j) (by omega) (a + j) e (by omega)
        · intro i hi1 hi2
          exact hfree i (by omega) (by rw [hpt] at hi2; exact hi2)
        · rw [hpt]; exact hae
        · rw [hpt]; exact hea
        · rw [hpt]; exact hcard

lemma pair (hC : ClustersZ j th) {f g : ℤ} (hf : th f) (hg : th g) (hfg : f < g)
    (hgf : g ≤ f + j) :
    (∀ i : ℤ, f < i → i < g → ¬ th i) ∧ (∀ i : ℤ, g < i → i ≤ g + j → ¬ th i) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = g - f := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  have hgk : g - (k : ℤ) = f := by omega
  rcases hC g hg with h1 | ⟨d, hd1, hdj, _hgd, hrest⟩
  · exact absurd (by rw [hgk]; exact hf) (h1 k (by omega) (by omega))
  have hkd : k = d := by
    by_contra hne
    exact hrest k (by omega) (by omega) hne (by rw [hgk]; exact hf)
  constructor
  · intro i hi1 hi2 hi
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k' : ℤ) = g - i := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    exact hrest k' (by omega) (by omega) (by omega) (by rw [show g - (k' : ℤ) = i by omega]; exact hi)
  · intro h hh1 hh2 hh
    obtain ⟨k'', hk''⟩ : ∃ k'' : ℕ, (k'' : ℤ) = h - g := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    have hhk : h - (k'' : ℤ) = g := by omega
    rcases hC h hh with h1' | ⟨d', hd1', hdj', _hhd, hrest'⟩
    · exact h1' k'' (by omega) (by omega) (by rw [hhk]; exact hg)
    have hkd' : k'' = d' := by
      by_contra hne
      exact hrest' k'' (by omega) (by omega) hne (by rw [hhk]; exact hg)
    obtain ⟨k3, hk3⟩ : ∃ k3 : ℕ, (k3 : ℤ) = h - f := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    exact hrest' k3 (by omega) (by omega) (by omega) (by rw [show h - (k3 : ℤ) = f by omega]; exact hf)

lemma cluster_chain (hC : ClustersZ j th) (hj : 1 ≤ j) (B : ℤ) (hB : th B)
    (hBl : ∀ i : ℤ, B < i → i ≤ B + j → ¬ th i) :
    ∀ (N : ℕ) (a : ℤ), B - a ≤ N → a < B → (∀ i : ℤ, a < i → i ≤ a + j → ¬ th i) →
      Chain j th a B := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a hN haB hfree
    have hex : ∃ k : ℕ, th (a + 1 + k) :=
      ⟨(B - a - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; convert hB using 1; ring⟩
    set k0 := Nat.find hex with hk0
    have hfth : th (a + 1 + k0) := Nat.find_spec hex
    have hkB : k0 ≤ (B - a - 1).toNat :=
      Nat.find_min' hex (by rw [Int.toNat_of_nonneg (by omega)]; convert hB using 1; ring)
    have hkB' : a + 1 + (k0 : ℤ) ≤ B := by
      have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ B - a - 1 by omega)
      omega
    have hmin : ∀ i : ℤ, a < i → i < a + 1 + k0 → ¬ th i := by
      intro i hi1 hi2 hi
      obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k' : ℤ) = i - a - 1 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
      have hlt : k' < k0 := by omega
      exact Nat.find_min hex hlt (by rw [show a + 1 + (k' : ℤ) = i by omega]; exact hi)
    set f : ℤ := a + 1 + k0 with hfdef
    have hfa : a + j < f := by
      by_contra hc
      push Not at hc
      exact hfree f (by omega) hc hfth
    obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = f - 1 - a := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    have hsfree : ∀ i : ℤ, a < i → i ≤ a + s → ¬ th i := fun i h1 h2 => hmin i h1 (by omega)

    have cont : ∀ e : ℤ, a < e → e ≤ B → (∀ i : ℤ, e < i → i ≤ e + j → ¬ th i) →
        Chain j th a e → Chain j th a B := by
      intro e hae heB hel hc
      rcases eq_or_lt_of_le heB with h | h
      · rw [← h]; exact hc
      · obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (N' : ℤ) = B - e := ⟨_, Int.toNat_of_nonneg (by omega)⟩
        exact chain_trans hc (ih N' (by omega) e (by omega) h hel)
    by_cases hl : ∀ i : ℤ, f < i → i ≤ f + j → ¬ th i
    · apply cont f (by omega) hkB' hl
      apply fill hj s a f (by omega) hsfree (by omega) (by omega)
      calc ((Finset.Ioc (a + s) f).filter th).card ≤ (Finset.Ioc (a + s) f).card :=
            Finset.card_filter_le _ _
        _ = 1 := by rw [Int.card_Ioc, show f - (a + s) = 1 by omega]; rfl
        _ ≤ 2 := by norm_num
    · push Not at hl
      obtain ⟨g, hfg, hgf, hg⟩ := hl
      obtain ⟨hmid, hgl⟩ := pair hC hfth hg hfg hgf
      have hgB : g ≤ B := by
        by_contra hc
        push Not at hc
        rcases eq_or_lt_of_le hkB' with h | h
        · exact hBl g (by omega) (by omega) hg
        · exact hmid B h hc hB
      apply cont g (by omega) hgB hgl
      apply fill hj s a g (by omega) hsfree (by omega) (by omega)
      calc ((Finset.Ioc (a + s) g).filter th).card ≤ ({f, g} : Finset ℤ).card := by
            apply Finset.card_le_card
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_Ioc] at hi
            simp only [Finset.mem_insert, Finset.mem_singleton]
            by_contra hc
            push Not at hc
            exact hmid i (by omega) (lt_of_le_of_ne hi.1.2 hc.2) hi.2
        _ ≤ 2 := Finset.card_le_two

lemma main (n : ℕ) (hj : 1 ≤ j) (hn : j + 1 ≤ n) (hper : ∀ i : ℤ, th (i + n) ↔ th i)
    (hC : ClustersZ j th) : ∃ a : ℤ, Chain j th a (a + n) := by
  by_cases hex : ∃ t : ℤ, th t
  · obtain ⟨t0, ht0⟩ := hex
    obtain ⟨t, ht, htl⟩ : ∃ t : ℤ, th t ∧ ∀ i : ℤ, t < i → i ≤ t + j → ¬ th i := by
      by_cases hl : ∀ i : ℤ, t0 < i → i ≤ t0 + j → ¬ th i
      · exact ⟨t0, ht0, hl⟩
      · push Not at hl
        obtain ⟨g, h1, h2, hg⟩ := hl
        exact ⟨g, hg, (pair hC ht0 hg h1 h2).2⟩
    refine ⟨t, cluster_chain hC hj (t + n) ((hper t).2 ht) ?_ n t (by omega) (by omega) htl⟩
    intro i hi1 hi2 hi
    have : th (i - n) := (hper (i - n)).1 (by rw [sub_add_cancel]; exact hi)
    exact htl (i - n) (by omega) (by omega) this
  · push Not at hex
    refine ⟨0, fill hj n 0 (0 + n) (by omega) (fun i _ _ => hex i) (by omega) (by omega) ?_⟩
    rw [Finset.filter_false_of_mem (fun i _ => hex i)]
    simp

end ClusterCuts

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
