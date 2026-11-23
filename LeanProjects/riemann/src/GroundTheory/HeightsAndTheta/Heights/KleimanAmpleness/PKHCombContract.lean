import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombContractSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHCombContract

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def ins (k : K) (i₀ : ι k) (T : ∀ k, Finset (ι k)) : ∀ k, Finset (ι k) :=
  Function.update T k (insert i₀ (T k))

def rem (T : ∀ k, Finset (ι k)) (l : K) (i : ι l) : ∀ k, Finset (ι k) :=
  Function.update T l ((T l).erase i)

theorem sum_card_update_of_mem (T : ∀ k, Finset (ι k)) (l : K) (A : Finset (ι l)) (s : Finset K) (hl : l ∈ s) :
    (∑ x ∈ s, ((Function.update T l A x).card - 1)) + ((T l).card - 1) =
      (∑ x ∈ s, ((T x).card - 1)) + (A.card - 1) := by
  rw [← Finset.add_sum_erase s _ hl, ← Finset.add_sum_erase s (fun x => (T x).card - 1) hl, Function.update_self]
  have : ∑ x ∈ s.erase l, ((Function.update T l A x).card - 1) = ∑ x ∈ s.erase l, ((T x).card - 1) :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]; ring

theorem sum_card_update_of_notMem (T : ∀ k, Finset (ι k)) (l : K) (A : Finset (ι l)) (s : Finset K) (hl : l ∉ s) :
    ∑ x ∈ s, ((Function.update T l A x).card - 1) = ∑ x ∈ s, ((T x).card - 1) :=
  Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (by rintro rfl; exact hl hx)]

theorem faceSign_eq (T : ∀ k, Finset (ι k)) (l : K) (i : ι l) :
    KH.faceSign T l i = (-1) ^ ((T l).filter (· < i)).card *
      (-1) ^ ∑ x ∈ Finset.univ.filter (· < l), ((T x).card - 1) := by
  rw [KH.faceSign, pow_add]

theorem faceSign_mul_self (T : ∀ k, Finset (ι k)) (l : K) (i : ι l) :
    KH.faceSign T l i * KH.faceSign T l i = 1 := by
  rw [KH.faceSign, ← mul_pow]; norm_num

theorem sign_lt (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hlk : l < k)
    (hi : i ∈ T l) (hcard : 2 ≤ (T l).card) :
    KH.faceSign (ins k i₀ (rem T l i)) k i₀ = - KH.faceSign (ins k i₀ T) k i₀ ∧
      KH.faceSign (ins k i₀ T) l i = KH.faceSign T l i := by
  have hne : k ≠ l := hlk.ne'
  constructor
  · have hmem : l ∈ Finset.univ.filter (· < k) := by simp [hlk]
    have hk : k ∉ Finset.univ.filter (· < k) := by simp
    have h1 := sum_card_update_of_mem T l ((T l).erase i) _ hmem
    rw [Finset.card_erase_of_mem hi] at h1
    rw [faceSign_eq, faceSign_eq, ins, ins, rem, Function.update_self, Function.update_self,
      Function.update_of_ne hne, sum_card_update_of_notMem _ _ _ _ hk, sum_card_update_of_notMem _ _ _ _ hk]
    have h2 : ∑ x ∈ Finset.univ.filter (· < k), ((T x).card - 1) =
        (∑ x ∈ Finset.univ.filter (· < k), ((Function.update T l ((T l).erase i) x).card - 1)) + 1 := by omega
    rw [h2, pow_succ]; ring
  · have hk : k ∉ Finset.univ.filter (· < l) := by simp [hlk.le]
    rw [faceSign_eq, faceSign_eq, ins, Function.update_of_ne hne.symm, sum_card_update_of_notMem _ _ _ _ hk]

theorem sign_gt (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hkl : k < l)
    (hk0 : i₀ ∉ T k) (hkne : (T k).Nonempty) :
    KH.faceSign (ins k i₀ (rem T l i)) k i₀ = KH.faceSign (ins k i₀ T) k i₀ ∧
      KH.faceSign (ins k i₀ T) l i = - KH.faceSign T l i := by
  have hne : l ≠ k := hkl.ne'
  constructor
  · have hl : l ∉ Finset.univ.filter (· < k) := by simp [hkl.le]
    have hk : k ∉ Finset.univ.filter (· < k) := by simp
    rw [faceSign_eq, faceSign_eq, ins, ins, rem, Function.update_self, Function.update_self,
      Function.update_of_ne hne.symm, sum_card_update_of_notMem _ _ _ _ hk, sum_card_update_of_notMem _ _ _ _ hk,
      sum_card_update_of_notMem _ _ _ _ hl]
  · have hmem : k ∈ Finset.univ.filter (· < l) := by simp [hkl]
    have h1 := sum_card_update_of_mem T k (insert i₀ (T k)) _ hmem
    rw [Finset.card_insert_of_notMem hk0] at h1
    have hpos := hkne.card_pos
    rw [faceSign_eq, faceSign_eq, ins, Function.update_of_ne hne]
    have h2 : ∑ x ∈ Finset.univ.filter (· < l), ((Function.update T k (insert i₀ (T k)) x).card - 1) =
        (∑ x ∈ Finset.univ.filter (· < l), ((T x).card - 1)) + 1 := by omega
    rw [h2, pow_succ]; ring

theorem sign_eq (T : ∀ k, Finset (ι k)) (k : K) (i₀ i : ι k) (hi : i ∈ T k) (hk0 : i₀ ∉ T k) :
    KH.faceSign T k i * KH.faceSign (ins k i₀ (rem T k i)) k i₀ =
      - (KH.faceSign (ins k i₀ T) k i₀ * KH.faceSign (ins k i₀ T) k i) := by
  have hne : i ≠ i₀ := fun h => hk0 (h ▸ hi)
  have hk : k ∉ Finset.univ.filter (· < k) := by simp
  rw [faceSign_eq, faceSign_eq, faceSign_eq, faceSign_eq, ins, ins, rem, Function.update_self,
    Function.update_self, Function.update_self, sum_card_update_of_notMem _ _ _ _ hk,
    sum_card_update_of_notMem _ _ _ _ hk, sum_card_update_of_notMem _ _ _ _ hk]
  set C := ∑ x ∈ Finset.univ.filter (· < k), ((T x).card - 1)
  have hb : (insert i₀ (T k)).filter (· < i₀) = (T k).filter (· < i₀) := by simp [Finset.filter_insert]
  have hb2 : (insert i₀ ((T k).erase i)).filter (· < i₀) = ((T k).filter (· < i₀)).erase i := by
    simp [Finset.filter_insert, Finset.filter_erase]
  rw [hb, hb2]
  rcases lt_or_gt_of_ne hne with h | h
  · have ha : (insert i₀ (T k)).filter (· < i) = (T k).filter (· < i) := by
      simp [Finset.filter_insert, not_lt.mpr h.le]
    rw [ha]
    have hm : i ∈ (T k).filter (· < i₀) := Finset.mem_filter.mpr ⟨hi, h⟩
    have hc := Finset.card_erase_of_mem hm
    have hp := Finset.card_pos.mpr ⟨i, hm⟩
    have : ((T k).filter (· < i₀)).card = (((T k).filter (· < i₀)).erase i).card + 1 := by omega
    rw [this, pow_succ]; ring
  · have ha : (insert i₀ (T k)).filter (· < i) = insert i₀ ((T k).filter (· < i)) := by
      simp [Finset.filter_insert, h]
    rw [ha, Finset.card_insert_of_notMem (fun hm => hk0 (Finset.mem_filter.mp hm).1)]
    have hm : i ∉ (T k).filter (· < i₀) := fun hm => absurd (Finset.mem_filter.mp hm).2 (not_lt.mpr h.le)
    rw [Finset.erase_eq_of_notMem hm, pow_succ]; ring

section Total

variable {S : Type} [CommRing S]

def tD (F : (∀ k, Finset (ι k)) → S) (T : ∀ k, Finset (ι k)) : S :=
  ∑ p ∈ Finset.univ.sigma T, KH.faceSign T p.1 p.2 • F (rem T p.1 p.2)

def tH (k : K) (i₀ : ι k) (F : (∀ k, Finset (ι k)) → S) (T : ∀ k, Finset (ι k)) : S :=
  if i₀ ∈ T k then 0 else KH.faceSign (ins k i₀ T) k i₀ • F (ins k i₀ T)

theorem tD_add (F₁ F₂ : (∀ k, Finset (ι k)) → S) (T : ∀ k, Finset (ι k)) :
    tD (fun T' => F₁ T' + F₂ T') T = tD F₁ T + tD F₂ T := by
  simp only [tD, smul_add, Finset.sum_add_distrib]

theorem sigma_ins (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) :
    Finset.univ.sigma (ins k i₀ T) = insert ⟨k, i₀⟩ (Finset.univ.sigma T) := by
  ext ⟨l, i⟩
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases h : l = k
  · subst h; simp [ins]
  · simp [ins, h]

theorem rem_ins_self (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (h : i₀ ∉ T k) :
    rem (ins k i₀ T) k i₀ = T := by
  rw [rem, ins, Function.update_self, Finset.erase_insert h, Function.update_idem, Function.update_eq_self]

theorem ins_rem_self (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (h : i₀ ∈ T k) :
    ins k i₀ (rem T k i₀) = T := by
  rw [ins, rem, Function.update_self, Finset.insert_erase h, Function.update_idem, Function.update_eq_self]

theorem rem_ins_comm (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hi : i ∈ T l)
    (h0 : i₀ ∉ T k) : rem (ins k i₀ T) l i = ins k i₀ (rem T l i) := by
  by_cases h : l = k
  · subst h
    have hne : i₀ ≠ i := fun e => h0 (e ▸ hi)
    rw [rem, ins, ins, rem, Function.update_self, Function.update_self, Function.update_idem,
      Function.update_idem, Finset.erase_insert_of_ne hne]
  · rw [rem, ins, ins, rem, Function.update_of_ne h, Function.update_of_ne (Ne.symm h),
      Function.update_comm (Ne.symm h)]

theorem mem_rem_iff (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) :
    i₀ ∈ rem T l i k ↔ i₀ ∈ T k ∧ (⟨l, i⟩ : Σ k, ι k) ≠ ⟨k, i₀⟩ := by
  by_cases h : l = k
  · subst h
    simp only [rem, Function.update_self, Finset.mem_erase, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    tauto
  · simp only [rem, Function.update_of_ne (Ne.symm h), ne_eq, Sigma.mk.inj_iff, h, false_and, not_false_eq_true,
      and_true]

theorem tD_tH (k : K) (i₀ : ι k) (F : (∀ k, Finset (ι k)) → S) (hF : ∀ T, (∃ l, T l = ∅) → F T = 0)
    (T : ∀ k, Finset (ι k)) (hT : ∀ l, (T l).Nonempty) :
    tD (tH k i₀ F) T + tH k i₀ (tD F) T = F T := by
  by_cases h0 : i₀ ∈ T k
  · have hH : tH k i₀ (tD F) T = 0 := if_pos h0
    rw [hH, add_zero, tD, Finset.sum_eq_single_of_mem (⟨k, i₀⟩ : Σ k, ι k) (by simp [h0])]
    · have hn : i₀ ∉ rem T k i₀ k := by simp [mem_rem_iff]
      rw [tH, if_neg hn, ins_rem_self T k i₀ h0, smul_smul, faceSign_mul_self, one_smul]
    · rintro ⟨l, i⟩ - hne
      have hm : i₀ ∈ rem T l i k := (mem_rem_iff T k i₀ l i).mpr ⟨h0, hne⟩
      rw [tH, if_pos hm, smul_zero]
  · have hkne := hT k
    have hH : tH k i₀ (tD F) T = KH.faceSign (ins k i₀ T) k i₀ • tD F (ins k i₀ T) := if_neg h0
    have hD : tD F (ins k i₀ T) = ∑ p ∈ Finset.univ.sigma (ins k i₀ T),
        KH.faceSign (ins k i₀ T) p.1 p.2 • F (rem (ins k i₀ T) p.1 p.2) := rfl
    rw [hH, hD, sigma_ins,
      Finset.sum_insert (by simp [h0]), rem_ins_self T k i₀ h0, smul_add, smul_smul, faceSign_mul_self, one_smul]
    have key : tD (tH k i₀ F) T + KH.faceSign (ins k i₀ T) k i₀ •
        ∑ p ∈ Finset.univ.sigma T, KH.faceSign (ins k i₀ T) p.1 p.2 • F (rem (ins k i₀ T) p.1 p.2) = 0 := by
      rw [tD, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨l, i⟩ := p
      have hi : i ∈ T l := (Finset.mem_sigma.mp hp).2
      have hn : i₀ ∉ rem T l i k := fun hm => h0 ((mem_rem_iff T k i₀ l i).mp hm).1
      rw [tH, if_neg hn, rem_ins_comm T k i₀ l i hi h0, smul_smul, smul_smul, ← add_smul]
      by_cases hz : F (ins k i₀ (rem T l i)) = 0
      · rw [hz, smul_zero]
      have hne : ∀ l', (ins k i₀ (rem T l i) l').Nonempty := by
        intro l'
        by_contra hc
        exact hz (hF _ ⟨l', Finset.not_nonempty_iff_eq_empty.mp hc⟩)
      rcases lt_trichotomy l k with hlk | rfl | hkl
      · have hcard : 2 ≤ (T l).card := by
          have h1 := (hne l).card_pos
          rw [ins, Function.update_of_ne hlk.ne, rem, Function.update_self, Finset.card_erase_of_mem hi] at h1
          omega
        obtain ⟨h1, h2⟩ := sign_lt T k i₀ l i hlk hi hcard
        rw [h1, h2, show KH.faceSign T l i * -KH.faceSign (ins k i₀ T) k i₀ +
          KH.faceSign (ins k i₀ T) k i₀ * KH.faceSign T l i = 0 by ring, zero_smul]
      · rw [sign_eq T l i₀ i hi h0, neg_add_cancel, zero_smul]
      · obtain ⟨h1, h2⟩ := sign_gt T k i₀ l i hkl h0 hkne
        rw [h1, h2, show KH.faceSign T l i * KH.faceSign (ins k i₀ T) k i₀ +
          KH.faceSign (ins k i₀ T) k i₀ * -KH.faceSign T l i = 0 by ring, zero_smul]
    rw [add_left_comm, key, add_zero]

end Total

section Complex

variable {S : Type} [CommRing S]

open Classical in

def ext (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (T : ∀ k, Finset (ι k)) : S :=
  if h : ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = n) ∧ ∀ l, J l ⊆ T l then φ ⟨⟨T, h.1⟩, h.2⟩ else 0

theorem ext_of_empty (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (T : ∀ k, Finset (ι k))
    (hT : ∃ l, T l = ∅) : ext J n φ T = 0 := by
  obtain ⟨l, hl⟩ := hT
  rw [ext, dif_neg]
  intro h
  have := h.1.1 l
  rw [hl] at this
  exact Finset.not_nonempty_empty this

theorem ext_cell (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (I : CombCell ι J n) :
    ext J n φ I.1.1 = φ I := by
  rw [ext, dif_pos ⟨I.1.2, I.2⟩]
  rfl

theorem ext_zero (J : ∀ k, Finset (ι k)) (n : ℕ) : ext J n (0 : CombC S J n) = 0 := by
  funext T
  rw [ext]
  split_ifs <;> rfl

theorem combD_apply (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n φ I = tD (ext J n φ) I.1.1 := by
  rw [tD, Finset.sum_sigma]
  simp only [combD, LinearMap.pi_apply, LinearMap.sum_apply, rem]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ((∀ l', (Function.update I.1.1 l ((I.1.1 l).erase i) l').Nonempty) ∧
      ∑ l', ((Function.update I.1.1 l ((I.1.1 l).erase i) l').card - 1) = n) ∧
      ∀ l', J l' ⊆ Function.update I.1.1 l ((I.1.1 l).erase i) l'
  · rw [dif_pos h, ext, dif_pos h]; rfl
  · rw [dif_neg h, ext, dif_neg h]; simp

theorem cond_ins (J : ∀ k, Finset (ι k)) (d : ℕ) (k : K) (i₀ : ι k) (T : ∀ k, Finset (ι k)) (h0 : i₀ ∉ T k)
    (h : ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = d) ∧ ∀ l, J l ⊆ T l) :
    ((∀ l, (ins k i₀ T l).Nonempty) ∧ ∑ l, ((ins k i₀ T l).card - 1) = d + 1) ∧ ∀ l, J l ⊆ ins k i₀ T l := by
  obtain ⟨⟨hne, hsum⟩, hJ⟩ := h
  refine ⟨⟨fun l => ?_, ?_⟩, fun l => ?_⟩
  · by_cases hl : l = k
    · subst hl; rw [ins, Function.update_self]; exact Finset.insert_nonempty _ _
    · rw [ins, Function.update_of_ne hl]; exact hne l
  · have h1 := sum_card_update_of_mem T k (insert i₀ (T k)) Finset.univ (Finset.mem_univ _)
    rw [Finset.card_insert_of_notMem h0] at h1
    have := (hne k).card_pos
    rw [ins]; omega
  · by_cases hl : l = k
    · subst hl; rw [ins, Function.update_self]; exact (hJ l).trans (Finset.subset_insert _ _)
    · rw [ins, Function.update_of_ne hl]; exact hJ l

theorem cond_of_ins (J : ∀ k, Finset (ι k)) (d : ℕ) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (T : ∀ k, Finset (ι k))
    (h0 : i₀ ∉ T k) (hk : (T k).Nonempty)
    (h : ((∀ l, (ins k i₀ T l).Nonempty) ∧ ∑ l, ((ins k i₀ T l).card - 1) = d + 1) ∧ ∀ l, J l ⊆ ins k i₀ T l) :
    ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = d) ∧ ∀ l, J l ⊆ T l := by
  obtain ⟨⟨hne, hsum⟩, hJ⟩ := h
  refine ⟨⟨fun l => ?_, ?_⟩, fun l => ?_⟩
  · by_cases hl : l = k
    · subst hl; exact hk
    · have := hne l; rwa [ins, Function.update_of_ne hl] at this
  · have h1 := sum_card_update_of_mem T k (insert i₀ (T k)) Finset.univ (Finset.mem_univ _)
    rw [Finset.card_insert_of_notMem h0] at h1
    have := hk.card_pos
    rw [ins] at hsum; omega
  · by_cases hl : l = k
    · subst hl
      have := hJ l
      rw [ins, Function.update_self] at this
      exact (Finset.subset_insert_iff_of_notMem hJ0).mp this
    · have := hJ l; rwa [ins, Function.update_of_ne hl] at this

def hh (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (m : ℕ) (φ : CombC S J (m + 1)) : CombC S J m :=
  fun I => tH k i₀ (ext J (m + 1) φ) I.1.1

theorem hh_zero (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (m : ℕ) : hh J k i₀ m (0 : CombC S J (m + 1)) = 0 := by
  funext I
  rw [hh, ext_zero, tH]
  split_ifs <;> simp

theorem ext_hh (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (m : ℕ) (φ : CombC S J (m + 1))
    (T : ∀ k, Finset (ι k)) (hk : (T k).Nonempty) :
    ext J m (hh J k i₀ m φ) T = tH k i₀ (ext J (m + 1) φ) T := by
  by_cases hc : ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = m) ∧ ∀ l, J l ⊆ T l
  · rw [ext, dif_pos hc]; rfl
  · rw [ext, dif_neg hc, tH]
    split_ifs with h0
    · rfl
    · rw [ext, dif_neg (fun h => hc (cond_of_ins J m k i₀ hJ0 T h0 hk h)), smul_zero]

theorem hh_combD (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (m : ℕ) (φ : CombC S J m) (I : CombCell ι J m) :
    hh J k i₀ m (combD S J m φ) I = tH k i₀ (tD (ext J m φ)) I.1.1 := by
  rw [hh, tH, tH]
  split_ifs with h0
  · rfl
  · rw [ext, dif_pos (cond_ins J m k i₀ I.1.1 h0 ⟨I.1.2, I.2⟩)]
    congr 1
    exact combD_apply J m φ _

def corr (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (d : ℕ) (φ : CombC S J d) (T : ∀ k, Finset (ι k)) : S :=
  if T k = ∅ then tH k i₀ (ext J d φ) T else 0

theorem tD_tH_succ (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (m : ℕ) (φ : CombC S J (m + 1))
    (I : CombCell ι J (m + 1)) :
    tD (tH k i₀ (ext J (m + 1) φ)) I.1.1 =
      combD S J m (hh J k i₀ m φ) I + tD (corr J k i₀ (m + 1) φ) I.1.1 := by
  have : tH k i₀ (ext J (m + 1) φ) = fun T => ext J m (hh J k i₀ m φ) T + corr J k i₀ (m + 1) φ T := by
    funext T
    rw [corr]
    by_cases hT : T k = ∅
    · rw [if_pos hT, ext_of_empty J m _ T ⟨k, hT⟩, zero_add]
    · rw [if_neg hT, add_zero, ext_hh J k i₀ hJ0 m φ T (Finset.nonempty_iff_ne_empty.mpr hT)]
  rw [this, tD_add, combD_apply]

theorem cell_card_eq_one_of_degree_zero (I : KH.Cell K ι 0) (l : K) : (I.1 l).card = 1 := by
  have h := I.2.2
  rw [Finset.sum_eq_zero_iff] at h
  have h1 := h l (Finset.mem_univ _)
  have h2 := (I.2.1 l).card_pos
  omega

theorem tD_tH_zero (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (φ : CombC S J 0) (I : CombCell ι J 0) :
    tD (tH k i₀ (ext J 0 φ)) I.1.1 = tD (corr J k i₀ 0 φ) I.1.1 := by
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨l, i⟩ := p
  have hi : i ∈ I.1.1 l := (Finset.mem_sigma.mp hp).2
  have hemp : (I.1.1 l).erase i = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_erase_of_mem hi, cell_card_eq_one_of_degree_zero I.1 l]
  congr 1
  rw [corr]
  split_ifs with hT
  · rfl
  · have hl : l ≠ k := by
      rintro rfl
      exact hT (by rw [rem, Function.update_self, hemp])
    rw [tH]
    split_ifs
    · rfl
    · rw [ext_of_empty J 0 φ _ ⟨l, by rw [ins, Function.update_of_ne hl, rem, Function.update_self, hemp]⟩,
        smul_zero]

end Complex

section Final

variable {S : Type} [CommRing S]

def repl (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (d : ℕ) (I : CombCell ι J d) (hJk : J k = ∅)
    (h1 : (I.1.1 k).card = 1) : CombCell ι J d :=
  ⟨⟨Function.update I.1.1 k {i₀}, fun l => by
      by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact Finset.singleton_nonempty _
      · rw [Function.update_of_ne hl]; exact I.1.2.1 l,
    by
      have h := sum_card_update_of_mem I.1.1 k {i₀} Finset.univ (Finset.mem_univ _)
      rw [Finset.card_singleton, h1, I.1.2.2] at h
      omega⟩, fun l => by
    show J l ⊆ Function.update I.1.1 k {i₀} l
    by_cases hl : l = k
    · subst hl; rw [hJk]; exact Finset.empty_subset _
    · rw [Function.update_of_ne hl]; exact I.2 l⟩

theorem corr_single (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (d : ℕ) (φ : CombC S J d) (I : CombCell ι J d)
    (hJk : J k = ∅) (h1 : (I.1.1 k).card = 1) :
    tD (corr J k i₀ d φ) I.1.1 = φ (repl J k i₀ d I hJk h1) := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
  rw [tD, Finset.sum_eq_single_of_mem (⟨k, i⟩ : Σ k, ι k) (by simp [hi])]
  · have hrem : rem I.1.1 k i = Function.update I.1.1 k ∅ := by rw [rem, hi, Finset.erase_singleton]
    have hins : ins k i₀ (Function.update I.1.1 k ∅) = Function.update I.1.1 k {i₀} := by
      rw [ins, Function.update_self, Function.update_idem, Finset.insert_empty]
    have hk : k ∉ Finset.univ.filter (· < k) := by simp
    have hs : KH.faceSign I.1.1 k i * KH.faceSign (Function.update I.1.1 k {i₀}) k i₀ = 1 := by
      rw [faceSign_eq, faceSign_eq, hi, Function.update_self, sum_card_update_of_notMem _ _ _ _ hk,
        Finset.filter_singleton, Finset.filter_singleton, if_neg (lt_irrefl i), if_neg (lt_irrefl i₀)]
      rw [Finset.card_empty, pow_zero, one_mul, ← mul_pow]
      norm_num
    rw [hrem, corr, if_pos (Function.update_self _ _ _), tH, if_neg (by simp), hins, smul_smul, hs, one_smul, ext,
      dif_pos ⟨(repl J k i₀ d I hJk h1).1.2, (repl J k i₀ d I hJk h1).2⟩]
    rfl
  · rintro ⟨l, j⟩ hp hne
    have hj : j ∈ I.1.1 l := (Finset.mem_sigma.mp hp).2
    rw [corr, if_neg, smul_zero]
    by_cases hl : l = k
    · subst hl
      rw [hi, Finset.mem_singleton] at hj
      subst hj
      exact absurd rfl hne
    · rw [rem, Function.update_of_ne (Ne.symm hl)]
      exact (I.1.2.1 k).ne_empty

theorem corr_zero (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (d : ℕ) (φ : CombC S J d)
    (I : CombCell ι J d) (h : ¬ (J k = ∅ ∧ (I.1.1 k).card = 1)) :
    tD (corr J k i₀ d φ) I.1.1 = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨l, j⟩ := p
  have hj : j ∈ I.1.1 l := (Finset.mem_sigma.mp hp).2
  rw [corr]
  split_ifs with hT
  swap
  · exact smul_zero _
  have hl : l = k := by
    by_contra hl
    rw [rem, Function.update_of_ne (Ne.symm hl)] at hT
    exact (I.1.2.1 k).ne_empty hT
  subst hl
  have hT' : (I.1.1 l).erase j = ∅ := by rw [rem, Function.update_self] at hT; exact hT
  have h1 : (I.1.1 l).card = 1 := by
    have := Finset.card_erase_of_mem hj
    rw [hT', Finset.card_empty] at this
    have := (I.1.2.1 l).card_pos
    omega
  have hJne : ¬ J l = ∅ := fun e => h ⟨e, h1⟩
  rw [tH, if_neg (by rw [hT]; exact Finset.notMem_empty _), ext, dif_neg]
  · simp
  rintro ⟨-, hJ⟩
  have hsub := hJ l
  rw [ins, Function.update_self, hT, Finset.insert_empty] at hsub
  rcases Finset.subset_singleton_iff.mp hsub with e | e
  · exact hJne e
  · exact hJ0 (e ▸ Finset.mem_singleton_self _)

theorem homotopy_succ (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (m : ℕ)
    (φ : CombC S J (m + 1)) (I : CombCell ι J (m + 1)) :
    combD S J m (hh J k i₀ m φ) I + hh J k i₀ (m + 1) (combD S J (m + 1) φ) I +
      tD (corr J k i₀ (m + 1) φ) I.1.1 = φ I := by
  have h := tD_tH k i₀ (ext J (m + 1) φ) (fun T hT => ext_of_empty J (m + 1) φ T hT) I.1.1 I.1.2.1
  rw [tD_tH_succ J k i₀ hJ0 m φ I, ← hh_combD, ext_cell] at h
  rw [← h]; abel

theorem homotopy_zero (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (φ : CombC S J 0) (I : CombCell ι J 0) :
    hh J k i₀ 0 (combD S J 0 φ) I + tD (corr J k i₀ 0 φ) I.1.1 = φ I := by
  have h := tD_tH k i₀ (ext J 0 φ) (fun T hT => ext_of_empty J 0 φ T hT) I.1.1 I.1.2.1
  rw [tD_tH_zero, ← hh_combD, ext_cell] at h
  rw [← h]; abel

end Final

theorem full : KHCombContract.Statement := by
  intro S _ K _ _ ι _ _ J n k i₀ hJ0 f hf
  suffices H : ∃ g : CombC S J n, f - g ∈ combB S J n ∧ ∀ I, g I = tD (corr J k i₀ n f) I.1.1 by
    obtain ⟨g, hg, hgI⟩ := H
    refine ⟨g, hg, fun I => ⟨fun h => ⟨repl J k i₀ n I h.1 h.2, Function.update_self _ _ _,
      fun l hl => Function.update_of_ne hl _ _, ?_⟩, fun h => ?_⟩⟩
    · rw [hgI, corr_single]
    · rw [hgI, corr_zero J k i₀ hJ0 n f I h]
  cases n with
  | zero =>
    refine ⟨f, ?_, fun I => ?_⟩
    · show f - f ∈ (⊥ : Submodule S (CombC S J 0))
      rw [sub_self]
      exact Submodule.zero_mem _
    · have h := homotopy_zero J k i₀ f I
      rw [hf, hh_zero, Pi.zero_apply, zero_add] at h
      exact h.symm
  | succ m =>
    refine ⟨f - combD S J m (hh J k i₀ m f), ?_, fun I => ?_⟩
    · show _ ∈ LinearMap.range (combD S J m)
      rw [sub_sub_cancel]
      exact LinearMap.mem_range_self _ _
    · have h := homotopy_succ J k i₀ hJ0 m f I
      rw [hf, hh_zero, Pi.zero_apply, add_zero] at h
      rw [Pi.sub_apply, ← h]
      abel

end KHCombContract

end

end GroundTheory.Heights₂.Heights.Kleiman
