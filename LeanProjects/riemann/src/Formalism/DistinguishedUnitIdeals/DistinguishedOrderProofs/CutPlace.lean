import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd

namespace Formalism.ExponentWindows

noncomputable def greedyStep (j : ℕ) (A F : ℕ → Prop) (x : ℕ) : ℕ := by
  classical
  exact if A (x + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + i) then x + j
    else sInf {y | x < y ∧ F y}

noncomputable def greedySeq (j : ℕ) (A F : ℕ → Prop) : ℕ → ℕ
  | 0 => 0
  | m + 1 => greedyStep j A F (greedySeq j A F m)

section Greedy

variable {n j : ℕ} {A F : ℕ → Prop}

lemma periodic_mul (hFper : ∀ y, F (y + n) ↔ F y) (y q : ℕ) : F (y + q * n) ↔ F y := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← add_assoc, hFper, ih]

lemma exists_gt_of_periodic (hn : 0 < n) (hF0 : F 0) (hFper : ∀ y, F (y + n) ↔ F y) (x : ℕ) :
    {y | x < y ∧ F y}.Nonempty := by
  refine ⟨(x + 1) * n, ?_, ?_⟩
  · nlinarith
  · have := (periodic_mul hFper 0 (x + 1)).mpr hF0
    simpa using this

lemma greedyStep_spec (hFA : ∀ y, F y → A y) (hn : 0 < n) (hF0 : F 0)
    (hFper : ∀ y, F (y + n) ↔ F y)
    (hsp : ∀ y, F y → ∀ i, 1 ≤ i → i < j → ¬ F (y + i))
    (hup : ∀ x, A x → (∀ i, 1 ≤ i → i < j → ¬ F (x + i)) →
      ¬ (A (x + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + i)) →
      ∃ y, x < y ∧ y ≤ x + 3 * j + 1 ∧ F y)
    (x : ℕ) (hAx : A x) (hIx : ∀ i, 1 ≤ i → i < j → ¬ F (x + i)) :
    x + j ≤ greedyStep j A F x ∧ greedyStep j A F x ≤ x + 3 * j + 1 ∧
    A (greedyStep j A F x) ∧ (∀ i, 1 ≤ i → i < j → ¬ F (greedyStep j A F x + i)) ∧
    (∀ y, F y → x < y → greedyStep j A F x ≤ y) := by
  classical
  unfold greedyStep
  split_ifs with hC
  · refine ⟨le_rfl, by omega, hC.1, ?_, ?_⟩
    · intro i hi1 hi2 hFi
      exact hC.2 (j + i) (by omega) (by omega) (by simpa [add_assoc] using hFi)
    · intro y hy hxy
      by_contra hlt
      push Not at hlt
      exact hIx (y - x) (by omega) (by omega) (by rwa [Nat.add_sub_cancel' hxy.le])
  · have hne := exists_gt_of_periodic hn hF0 hFper x
    obtain ⟨hlt, hFs⟩ := Nat.sInf_mem hne
    have hmin : ∀ y, x < y → F y → sInf {y | x < y ∧ F y} ≤ y :=
      fun y h1 h2 => Nat.sInf_le ⟨h1, h2⟩
    refine ⟨?_, ?_, hFA _ hFs, hsp _ hFs, fun y hy hxy => hmin y hxy hy⟩
    · by_contra h
      push Not at h
      exact hIx (sInf {y | x < y ∧ F y} - x) (by omega) (by omega)
        (by rwa [Nat.add_sub_cancel' hlt.le])
    · obtain ⟨y, h1, h2, h3⟩ := hup x hAx hIx hC
      exact (hmin y h1 h3).trans h2

lemma greedyStep_add (hn : 0 < n) (hF0 : F 0) (hFper : ∀ y, F (y + n) ↔ F y)
    (hAper : ∀ y, A (y + n) ↔ A y) (x : ℕ) :
    greedyStep j A F (x + n) = greedyStep j A F x + n := by
  classical
  unfold greedyStep
  have hC : (A (x + n + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + n + i)) ↔
      (A (x + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + i)) := by
    have e1 : x + n + j = (x + j) + n := by ring
    rw [e1, hAper]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    have e2 : x + n + i = (x + i) + n := by ring
    rw [e2, hFper]
  by_cases h : A (x + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + i)
  · rw [if_pos (hC.mpr h), if_pos h]; ring
  · rw [if_neg (mt hC.mp h), if_neg h]
    apply le_antisymm
    · obtain ⟨h1, h2⟩ := Nat.sInf_mem (exists_gt_of_periodic hn hF0 hFper x)
      exact Nat.sInf_le ⟨by omega, (hFper _).mpr h2⟩
    · obtain ⟨h1, h2⟩ := Nat.sInf_mem (exists_gt_of_periodic hn hF0 hFper (x + n))
      have key : sInf {y | x < y ∧ F y} ≤ sInf {y | x + n < y ∧ F y} - n := by
        apply Nat.sInf_le
        refine ⟨by omega, ?_⟩
        have := (hFper (sInf {y | x + n < y ∧ F y} - n)).mp
        rw [Nat.sub_add_cancel (by omega)] at this
        exact this h2
      omega

end Greedy

section GreedySeq

variable {n j : ℕ} {A F : ℕ → Prop}

lemma greedySeq_succ (m : ℕ) :
    greedySeq j A F (m + 1) = greedyStep j A F (greedySeq j A F m) := rfl

theorem greedy_seq_props (hj : 1 ≤ j) (hn : 0 < n) (hFA : ∀ y, F y → A y) (hF0 : F 0)
    (hFper : ∀ y, F (y + n) ↔ F y) (hAper : ∀ y, A (y + n) ↔ A y)
    (hsp : ∀ y, F y → ∀ i, 1 ≤ i → i < j → ¬ F (y + i))
    (hup : ∀ x, A x → (∀ i, 1 ≤ i → i < j → ¬ F (x + i)) →
      ¬ (A (x + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + i)) →
      ∃ y, x < y ∧ y ≤ x + 3 * j + 1 ∧ F y) :
    greedySeq j A F 0 = 0 ∧
    (∀ m, greedySeq j A F m + j ≤ greedySeq j A F (m + 1) ∧
      greedySeq j A F (m + 1) ≤ greedySeq j A F m + 3 * j + 1) ∧
    (∀ m, A (greedySeq j A F m)) ∧
    (∀ y, F y → ∃ m, greedySeq j A F m = y) ∧
    ∃ M, ∀ m, greedySeq j A F (m + M) = greedySeq j A F m + n := by
  classical
  set x := greedySeq j A F with hxdef
  have hinv : ∀ m, A (x m) ∧ ∀ i, 1 ≤ i → i < j → ¬ F (x m + i) := by
    intro m
    induction m with
    | zero => exact ⟨hFA 0 hF0, by simpa [hxdef, greedySeq] using hsp 0 hF0⟩
    | succ m ih =>
      obtain ⟨-, -, h3, h4, -⟩ := greedyStep_spec hFA hn hF0 hFper hsp hup (x m) ih.1 ih.2
      exact ⟨h3, h4⟩
  have hstep : ∀ m, x m + j ≤ x (m + 1) ∧ x (m + 1) ≤ x m + 3 * j + 1 ∧
      (∀ y, F y → x m < y → x (m + 1) ≤ y) := by
    intro m
    obtain ⟨h1, h2, -, -, h5⟩ := greedyStep_spec hFA hn hF0 hFper hsp hup (x m) (hinv m).1 (hinv m).2
    exact ⟨h1, h2, h5⟩
  have hx0 : x 0 = 0 := rfl
  have hgrow : ∀ m, m ≤ x m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => have := (hstep m).1; omega
  have hhit : ∀ y, F y → ∃ m, x m = y := by
    intro y hy
    have hex : ∃ m, y < x m := ⟨y + 1, by have := hgrow (y + 1); omega⟩
    have hm1 : y < x (Nat.find hex) := Nat.find_spec hex
    have hm1pos : Nat.find hex ≠ 0 := by
      intro h; rw [h, hx0] at hm1; omega
    obtain ⟨p, hp⟩ : ∃ p, Nat.find hex = p + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hle : x p ≤ y := by
      have := Nat.find_min hex (show p < Nat.find hex by omega)
      omega
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      have := (hstep p).2.2 y hy hlt
      rw [hp] at hm1
      omega
    · exact ⟨p, heq⟩
  have hFn : F n := by simpa using (hFper 0).mpr hF0
  obtain ⟨M, hM⟩ := hhit n hFn
  refine ⟨hx0, fun m => ⟨(hstep m).1, (hstep m).2.1⟩, fun m => (hinv m).1, hhit, M, ?_⟩
  intro m
  induction m with
  | zero => simp [hM, hx0]
  | succ m ih =>
    rw [show m + 1 + M = (m + M) + 1 by ring, hxdef, greedySeq_succ, greedySeq_succ, ← hxdef, ih,
      greedyStep_add hn hF0 hFper hAper]

end GreedySeq

section Cyclic

variable {n j : ℕ}

lemma range_shift (x : ℕ → ℕ) (hmono : StrictMono x) (hx0 : x 0 = 0) (M : ℕ)
    (hM : ∀ m, x (m + M) = x m + n) (r q : ℕ) :
    (∃ m, x m = r + q * n) ↔ ∃ m, x m = r := by
  have hup : ∀ m q, x (m + q * M) = x m + q * n := by
    intro m q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show m + (q + 1) * M = (m + q * M) + M by ring, hM, ih]; ring
  constructor
  · induction q with
    | zero => simp
    | succ q ih =>
      rintro ⟨m, hm⟩
      apply ih
      by_cases hmM : m < M
      · exfalso
        have h1 := hmono hmM
        have h2 := hM 0
        rw [zero_add, hx0, zero_add] at h2
        rw [h2] at h1
        nlinarith
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + M := ⟨m - M, by omega⟩
        refine ⟨m', ?_⟩
        rw [hM] at hm
        nlinarith
  · rintro ⟨m, hm⟩
    exact ⟨m + q * M, by rw [hup, hm]⟩

lemma range_mod (x : ℕ → ℕ) (hmono : StrictMono x) (hx0 : x 0 = 0) (M : ℕ)
    (hM : ∀ m, x (m + M) = x m + n) (y : ℕ) :
    (∃ m, x m = y) ↔ ∃ m, x m = y % n := by
  have := range_shift x hmono hx0 M hM (y % n) (y / n)
  rwa [Nat.mod_add_div'] at this

theorem pred_of_seq [NeZero n] (hj : 1 ≤ j) (b : ZMod n) (x : ℕ → ℕ) (hx0 : x 0 = 0)
    (hstep : ∀ m, x m + j ≤ x (m + 1) ∧ x (m + 1) ≤ x m + 3 * j + 1) (M : ℕ)
    (hM : ∀ m, x (m + M) = x m + n) (S : Finset (ZMod n))
    (hS : ∀ c, c ∈ S ↔ ∃ m, c = b + (x m : ZMod n)) (c : ZMod n) (hc : c ∈ S) :
    ∃ d : ℕ, j ≤ d ∧ d ≤ 3 * j + 1 ∧ c - (d : ZMod n) ∈ S ∧
      ∀ k : ℕ, 1 ≤ k → k < d → c - (k : ZMod n) ∉ S := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmono : StrictMono x := strictMono_nat_of_lt_succ (fun m => by have := (hstep m).1; omega)
  obtain ⟨m, rfl⟩ := (hS c).mp hc
  have hMpos : M ≠ 0 := by
    intro h; have := hM 0; simp only [h, add_zero] at this; omega
  obtain ⟨p, hp⟩ : ∃ p, m + M = p + 1 := ⟨m + M - 1, by omega⟩
  have hcast : (x m : ZMod n) = (x (p + 1) : ZMod n) := by
    rw [← hp, hM]; push_cast; simp
  have hle : x p ≤ x (p + 1) := (hstep p).1.trans' (Nat.le_add_right _ _)
  refine ⟨x (p + 1) - x p, by have := (hstep p).1; omega, by have := (hstep p).2; omega, ?_, ?_⟩
  · rw [hS]
    refine ⟨p, ?_⟩
    rw [hcast, Nat.cast_sub hle]; ring
  · intro k hk1 hk2 hk
    obtain ⟨m'', hm''⟩ := (hS _).mp hk
    have hkle : k ≤ x (p + 1) := by omega
    have h1 : ((x (p + 1) - k : ℕ) : ZMod n) = (x m'' : ZMod n) := by
      rw [Nat.cast_sub hkle, ← hcast]
      linear_combination hm''
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    have h2 : ∃ m3, x m3 = (x m'') % n := (range_mod x hmono hx0 M hM _).mp ⟨m'', rfl⟩
    rw [← h1] at h2
    obtain ⟨m3, hm3⟩ := (range_mod x hmono hx0 M hM _).mpr h2
    have h3 : x p < x m3 := by omega
    have h4 : x m3 < x (p + 1) := by omega
    rw [hmono.lt_iff_lt] at h3 h4
    omega

end Cyclic

section Letters

variable {n j : ℕ} [NeZero n] {thick : ZMod n → Prop}

lemma exists_end (H : ∀ a : ZMod n, thick a → ∀ k : ℕ, 1 ≤ k → k ≤ j → thick (a - k) →
      ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (a - k - k'))
    (t : ZMod n) (ht : thick t) :
    ∃ k : ℕ, k ≤ j ∧ thick (t + k) ∧ ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (t + k + k') := by
  by_cases hg : ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (t + k')
  · exact ⟨0, Nat.zero_le _, by simpa using ht, by simpa using hg⟩
  · push Not at hg
    obtain ⟨k, hk1, hk2, hk⟩ := hg
    refine ⟨k, hk2, hk, ?_⟩
    intro k' h1 h2 hk'
    have e1 : t + (k : ZMod n) + k' - k' = t + k := by ring
    have e2 : t + (k : ZMod n) + k' - k' - k = t := by ring
    have := H _ hk' k' h1 h2 (by rw [e1]; exact hk) k hk1 hk2
    rw [e2] at this
    exact this ht

lemma no_three (H : ∀ a : ZMod n, thick a → ∀ k : ℕ, 1 ≤ k → k ≤ j → thick (a - k) →
      ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (a - k - k'))
    (c : ZMod n) (k₁ k₂ k₃ : ℕ) (h12 : k₁ < k₂) (h23 : k₂ < k₃) (h3 : k₃ ≤ j)
    (t₁ : thick (c - k₁)) (t₂ : thick (c - k₂)) (t₃ : thick (c - k₃)) : False := by
  have e1 : c - (k₁ : ZMod n) - ((k₂ - k₁ : ℕ) : ZMod n) = c - k₂ := by
    rw [Nat.cast_sub h12.le]; ring
  have e2 : c - (k₁ : ZMod n) - ((k₂ - k₁ : ℕ) : ZMod n) - ((k₃ - k₂ : ℕ) : ZMod n) = c - k₃ := by
    rw [Nat.cast_sub h12.le, Nat.cast_sub h23.le]; ring
  have := H _ t₁ (k₂ - k₁) (by omega) (by omega) (by rw [e1]; exact t₂) (k₃ - k₂) (by omega) (by omega)
  rw [e2] at this
  exact this t₃

lemma card_le_two_of_no_three (P : ℕ → Prop) [DecidablePred P] (s : Finset ℕ)
    (h : ∀ a b c, a < b → b < c → a ∈ s → b ∈ s → c ∈ s → P a → P b → P c → False) :
    (s.filter P).card ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hc
  simp only [Finset.mem_filter] at ha hb hc'
  rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hbc with h3 | h3 <;>
    first
    | omega
    | exact h a b c (by omega) (by omega) ha.1 hb.1 hc'.1 ha.2 hb.2 hc'.2
    | exact h a c b (by omega) (by omega) ha.1 hc'.1 hb.1 ha.2 hc'.2 hb.2
    | exact h b a c (by omega) (by omega) hb.1 ha.1 hc'.1 hb.2 ha.2 hc'.2
    | exact h b c a (by omega) (by omega) hb.1 hc'.1 ha.1 hb.2 hc'.2 ha.2
    | exact h c a b (by omega) (by omega) hc'.1 ha.1 hb.1 hc'.2 ha.2 hb.2
    | exact h c b a (by omega) (by omega) hc'.1 hb.1 ha.1 hc'.2 hb.2 ha.2

end Letters

section Assembly

variable {n j : ℕ} [NeZero n] {thick : ZMod n → Prop} [DecidablePred thick]

theorem cuts_clauses (H : ∀ a : ZMod n, thick a → ∀ k : ℕ, 1 ≤ k → k ≤ j → thick (a - k) →
      ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (a - k - k'))
    (S : Finset (ZMod n)) (hne : S.Nonempty)
    (hgood : ∀ c ∈ S, ∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (c + k))
    (hend : ∀ e, thick e → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (e + k)) → e ∈ S)
    (hpred : ∀ c ∈ S, ∃ d : ℕ, j ≤ d ∧ d ≤ 3 * j + 1 ∧ c - (d : ZMod n) ∈ S ∧
      ∀ k : ℕ, 1 ≤ k → k < d → c - (k : ZMod n) ∉ S) :
    ∃ (cuts : Finset (ZMod n)) (ell : ZMod n → ℕ), cuts.Nonempty ∧
      ∀ c ∈ cuts,
        (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (c + k)) ∧
        j ≤ ell c ∧ ell c ≤ 3 * j + 1 ∧ ell c ≤ n ∧
        c - (ell c : ZMod n) ∈ cuts ∧ (∀ k : ℕ, 1 ≤ k → k < ell c → c - k ∉ cuts) ∧
        (∀ k : ℕ, k < ell c → thick (c - k) → k ≤ j) ∧
        ((Finset.range (ell c)).filter (fun k : ℕ => thick (c - (k : ZMod n)))).card ≤ 2 ∧
        (∀ k k' : ℕ, k < ell c → k' < ell c → thick (c - k) → thick (c - k') →
          k ≤ k' + j ∧ k' ≤ k + j) := by
  have hch : ∀ c, ∃ d : ℕ, c ∈ S → (j ≤ d ∧ d ≤ 3 * j + 1 ∧ c - (d : ZMod n) ∈ S ∧
      ∀ k : ℕ, 1 ≤ k → k < d → c - (k : ZMod n) ∉ S) := by
    intro c
    by_cases hc : c ∈ S
    · obtain ⟨d, hd⟩ := hpred c hc
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose ell hell using hch
  refine ⟨S, ell, hne, fun c hc => ?_⟩
  obtain ⟨hd1, hd2, hpr, hgap⟩ := hell c hc
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hdn : ell c ≤ n := by
    by_contra h
    push Not at h
    exact hgap n hnpos h (by simpa using hc)
  have harc : ∀ k : ℕ, k < ell c → thick (c - k) → k ≤ j := by
    intro k hk ht
    by_contra hkj
    push Not at hkj
    obtain ⟨k'', hk''1, hk''2, hk''3⟩ := exists_end H _ ht
    have he := hend _ hk''2 hk''3
    have e : c - (k : ZMod n) + k'' = c - ((k - k'' : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [e] at he
    exact hgap (k - k'') (by omega) (by omega) he
  refine ⟨hgood c hc, hd1, hd2, hdn, hpr, hgap, harc, ?_, ?_⟩
  · apply card_le_two_of_no_three
    intro a b c' hab hbc _ _ hc' ta tb tc
    exact no_three H c a b c' hab hbc (harc c' (Finset.mem_range.mp hc') tc) ta tb tc
  · intro k k' hk hk' ht ht'
    have := harc k hk ht
    have := harc k' hk' ht'
    omega

theorem exists_cut_set (hj : 1 ≤ j) (hn : j + 1 ≤ n)
    (H : ∀ a : ZMod n, thick a → ∀ k : ℕ, 1 ≤ k → k ≤ j → thick (a - k) →
      ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (a - k - k')) :
    ∃ S : Finset (ZMod n), S.Nonempty ∧
      (∀ c ∈ S, ∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (c + k)) ∧
      (∀ e, thick e → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (e + k)) → e ∈ S) ∧
      (∀ c ∈ S, ∃ d : ℕ, j ≤ d ∧ d ≤ 3 * j + 1 ∧ c - (d : ZMod n) ∈ S ∧
        ∀ k : ℕ, 1 ≤ k → k < d → c - (k : ZMod n) ∉ S) := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases hex : ∃ t, thick t
  · obtain ⟨t, ht⟩ := hex
    obtain ⟨k0, -, hb1, hb2⟩ := exists_end H t ht
    set b := t + (k0 : ZMod n) with hb
    let A : ℕ → Prop := fun y => ∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (b + (y : ZMod n) + k)
    let F : ℕ → Prop := fun y => thick (b + (y : ZMod n)) ∧ A y
    have hcast : ∀ y : ℕ, ((y + n : ℕ) : ZMod n) = (y : ZMod n) := by intro y; simp
    have hAper : ∀ y, A (y + n) ↔ A y := by intro y; simp only [A, hcast]
    have hFper : ∀ y, F (y + n) ↔ F y := by intro y; simp only [F, A, hcast]
    have hF0 : F 0 := ⟨by simpa using hb1, fun k h1 h2 => by simpa using hb2 k h1 h2⟩
    have hFA : ∀ y, F y → A y := fun y h => h.2
    have hsp : ∀ y, F y → ∀ i, 1 ≤ i → i < j → ¬ F (y + i) := by
      intro y hy i h1 h2 hyi
      have := hyi.1
      push_cast at this
      exact hy.2 i h1 h2.le (by rwa [add_assoc])
    have hup : ∀ x, A x → (∀ i, 1 ≤ i → i < j → ¬ F (x + i)) →
        ¬ (A (x + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + i)) →
        ∃ y, x < y ∧ y ≤ x + 3 * j + 1 ∧ F y := by
      intro x _ _ hC
      by_cases hA : A (x + j)
      · have : ¬ ∀ i, j < i → i < 2 * j → ¬ F (x + i) := fun h => hC ⟨hA, h⟩
        push Not at this
        obtain ⟨i, h1, h2, h3⟩ := this
        exact ⟨x + i, by omega, by omega, h3⟩
      · simp only [A, not_forall, not_not] at hA
        obtain ⟨k, hk1, hk2, hk⟩ := hA
        obtain ⟨k'', hk''1, hk''2, hk''3⟩ := exists_end H _ hk
        have e : b + ((x + j + k + k'' : ℕ) : ZMod n) =
            b + ((x + j : ℕ) : ZMod n) + k + k'' := by push_cast; ring
        refine ⟨x + j + k + k'', by omega, by omega, ?_, ?_⟩
        · rw [e]; exact hk''2
        · intro k' h1 h2; rw [e]; exact hk''3 k' h1 h2
    obtain ⟨hx0, hstep, hAx, hhit, M, hM⟩ :=
      greedy_seq_props (n := n) hj hnpos hFA hF0 hFper hAper hsp hup
    refine ⟨Finset.univ.filter (fun c => ∃ m, c = b + (greedySeq j A F m : ZMod n)),
      ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, by simp [hx0]⟩⟩, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨m, rfl⟩ := (Finset.mem_filter.mp hc).2
      exact hAx m
    · intro e he hg
      have hval : b + ((e - b).val : ZMod n) = e := by rw [ZMod.natCast_zmod_val]; ring
      obtain ⟨m, hm⟩ := hhit (e - b).val ⟨by rw [hval]; exact he, by
        intro k h1 h2; rw [hval]; exact hg k h1 h2⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, m, by rw [hm, hval]⟩
    · intro c hc
      exact pred_of_seq hj b _ hx0 hstep M hM _ (fun c => by simp) c hc
  · push Not at hex
    let A : ℕ → Prop := fun _ => True
    let F : ℕ → Prop := fun y => n ∣ y
    have hFA : ∀ y, F y → A y := fun _ _ => trivial
    have hF0 : F 0 := dvd_zero n
    have hFper : ∀ y, F (y + n) ↔ F y := fun y => Nat.dvd_add_self_right
    have hAper : ∀ y, A (y + n) ↔ A y := fun _ => Iff.rfl
    have hsp : ∀ y, F y → ∀ i, 1 ≤ i → i < j → ¬ F (y + i) := by
      intro y hy i h1 h2 hyi
      have := Nat.le_of_dvd (by omega) ((Nat.dvd_add_right hy).mp hyi)
      omega
    have hup : ∀ x, A x → (∀ i, 1 ≤ i → i < j → ¬ F (x + i)) →
        ¬ (A (x + j) ∧ ∀ i, j < i → i < 2 * j → ¬ F (x + i)) →
        ∃ y, x < y ∧ y ≤ x + 3 * j + 1 ∧ F y := by
      intro x _ _ hC
      have : ¬ ∀ i, j < i → i < 2 * j → ¬ F (x + i) := fun h => hC ⟨trivial, h⟩
      push Not at this
      obtain ⟨i, h1, h2, h3⟩ := this
      exact ⟨x + i, by omega, by omega, h3⟩
    obtain ⟨hx0, hstep, -, -, M, hM⟩ :=
      greedy_seq_props (n := n) hj hnpos hFA hF0 hFper hAper hsp hup
    refine ⟨Finset.univ.filter (fun c => ∃ m, c = (0 : ZMod n) + (greedySeq j A F m : ZMod n)),
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, by simp [hx0]⟩⟩, ?_, ?_, ?_⟩
    · intro c _ k _ _; exact hex _
    · intro e he; exact absurd he (hex e)
    · intro c hc
      exact pred_of_seq hj 0 _ hx0 hstep M hM _ (fun c => by simp) c hc

end Assembly

theorem exists_cuts_of_sparse_thick : CutPlace := by
  intro n j _ thick _ hj hn H
  obtain ⟨S, hne, hgood, hend, hpred⟩ := exists_cut_set hj hn H
  exact cuts_clauses H S hne hgood hend hpred

end Formalism.ExponentWindows
