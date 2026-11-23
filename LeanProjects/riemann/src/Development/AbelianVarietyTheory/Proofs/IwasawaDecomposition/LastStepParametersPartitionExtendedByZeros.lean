import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastStepParam

lemma lowK_allPos {n : ℕ} (lam : Fin n → ℝ) (a : Fin n) :
    Formalism.QuantumDeterminants.lowK (allPos n) lam a = lam a - ((n : ℝ) - 1) / 2 + ((a : ℕ) : ℝ) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have := a.2
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  simp only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, allPos, Pi.add_apply, Pi.sub_apply, ne_eq,
    not_true_eq_false, and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2,
    Fin.card_Ioi, Fin.card_Iio, h3]
  push_cast
  ring

lemma sub_mono {n : ℕ} {z : Fin n → ℤ} (hz : StrictMono z) (a d : ℕ) (h : a + d < n) :
    z ⟨a, by omega⟩ + d ≤ z ⟨a + d, h⟩ := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 : z ⟨a + d, by omega⟩ < z ⟨a + (d + 1), h⟩ := hz (by simp [Fin.lt_def])
    push_cast
    omega

lemma sub_mono' {n : ℕ} {z : Fin n → ℤ} (hz : StrictMono z) {a b : Fin n} (h : (a : ℕ) ≤ b) :
    z a - (a : ℕ) ≤ z b - (b : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ b from h)
  have := sub_mono hz a d hb
  push_cast
  omega

lemma shape {n t : ℕ} (e s : ℤ) (ht : (t : ℤ) = 2 * s + 1) (z : Fin n → ℤ) (hz : StrictMono z)
    (hb : ∀ a, -e + s + 2 ≤ z a) (lam' : Fin (n + t) → ℝ) (h' : StrictAnti lam')
    (hr : ∀ x : ℝ, x ∈ Set.range lam' ↔
      (∃ a, x = -(z a : ℝ)) ∨ ∃ c : ℕ, c < t ∧ x = ((e + s - c : ℤ) : ℝ)) (b : Fin (n + t)) :
    lam' b = ((if h : (b : ℕ) < t then e + s - (b : ℕ) else -z ⟨b - t, by omega⟩ : ℤ) : ℝ) := by
  let L : Fin (n + t) → ℤ := fun b => if h : (b : ℕ) < t then e + s - (b : ℕ) else -z ⟨b - t, by omega⟩
  have hL : StrictAnti L := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    simp only [L]
    split_ifs with h1 h2 h2
    · omega
    · omega
    · have := hb ⟨b - t, by omega⟩
      omega
    · have : z ⟨a - t, by omega⟩ < z ⟨b - t, by omega⟩ := hz (by simp only [Fin.lt_def]; omega)
      omega
  have hL' : StrictAnti fun b => (L b : ℝ) := fun a b hab => by
    have := hL hab
    simp only
    exact_mod_cast this
  have key : lam' = fun b => (L b : ℝ) := by
    rw [← StrictAnti.range_inj h' hL']
    ext x
    rw [hr]
    constructor
    · rintro (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
      · refine ⟨⟨a + t, by omega⟩, ?_⟩
        simp [L]
      · refine ⟨⟨c, by omega⟩, ?_⟩
        simp [L, hc]
    · rintro ⟨c, rfl⟩
      by_cases hc : (c : ℕ) < t
      · exact .inr ⟨c, hc, by simp [L, hc]⟩
      · exact .inl ⟨⟨c - t, by omega⟩, by simp [L, hc]⟩
  rw [key]

lemma partition {n t : ℕ} (e s p : ℤ) (ht : (t : ℤ) = 2 * s + 1) (hn : (n : ℤ) = 2 * p)
    (z : Fin n → ℤ) (lam : Fin n → ℝ) (hl : StrictAnti lam) (hlz : ∀ a, lam a = -(z a : ℝ) + 1 / 2)
    (hb : ∀ a, -e + s + 2 ≤ z a) (lam' : Fin (n + t) → ℝ) (h' : StrictAnti lam')
    (hr : ∀ x : ℝ, x ∈ Set.range lam' ↔
      (∃ a, x = -(z a : ℝ)) ∨ ∃ c : ℕ, c < t ∧ x = ((e + s - c : ℤ) : ℝ)) :
    ∃ (hn : n ≤ n + t) (ν : Fin (n + t) → ℕ), Antitone ν ∧ (∀ b : Fin (n + t), n ≤ (b : ℕ) → ν b = 0) ∧
      (∀ a, Formalism.QuantumDeterminants.lowK (allPos n) lam a = ((e - p - s : ℤ) : ℝ) - ν (Fin.castLE hn (Fin.rev a))) ∧
      ∀ b, Formalism.QuantumDeterminants.lowK (allPos (n + t)) lam' b = -((-e + p : ℤ) : ℝ) - ν (Fin.rev b) := by
  have hz : StrictMono z := fun a b hab => by
    have := hl hab
    rw [hlz, hlz] at this
    have h2 : (z a : ℝ) < z b := by linarith
    exact_mod_cast h2
  have hpos : ∀ a : Fin n, 0 ≤ e + z a - (s + 1) - (a : ℕ) := fun a => by
    have h1 := sub_mono' hz (a := ⟨0, by have := a.2; omega⟩) (b := a) (Nat.zero_le _)
    have h2 := hb ⟨0, by have := a.2; omega⟩
    simp only [Nat.cast_zero] at h1
    omega
  have htR : (t : ℝ) = 2 * s + 1 := by exact_mod_cast ht
  have hnR : (n : ℝ) = 2 * p := by exact_mod_cast hn
  let ν : Fin (n + t) → ℕ := fun c => if h : (c : ℕ) < n then
    (e + z ⟨n - 1 - c, by omega⟩ - (s + 1) - ((n - 1 - c : ℕ) : ℤ)).toNat else 0
  have hν : ∀ (c : Fin (n + t)) (a : Fin n), (c : ℕ) + a + 1 = n →
      (ν c : ℝ) = e + z a - (s + 1) - (a : ℕ) := by
    intro c a h
    have hc : (c : ℕ) < n := by omega
    have ha : (⟨n - 1 - c, by omega⟩ : Fin n) = a := Fin.ext (by simp only; omega)
    have ha' : n - 1 - c = a := by omega
    have : (ν c : ℤ) = e + z a - (s + 1) - (a : ℕ) := by
      simp only [ν, dif_pos hc, ha]
      rw [ha']
      exact Int.toNat_of_nonneg (hpos a)
    exact_mod_cast this
  refine ⟨by omega, ν, ?_, ?_, ?_, ?_⟩
  · intro c d hcd
    have hcd' : (c : ℕ) ≤ d := hcd
    simp only [ν]
    split_ifs with h1 h2 h2
    · apply Int.toNat_le_toNat
      have := sub_mono' hz (a := ⟨n - 1 - d, by omega⟩) (b := ⟨n - 1 - c, by omega⟩) (by simp only; omega)
      simp only at this
      omega
    · omega
    · omega
    · omega
  · intro b hb
    simp only [ν]
    rw [dif_neg (by omega)]
  · intro a
    have := a.2
    rw [lowK_allPos, hν _ a (by simp [Fin.val_rev]; omega), hlz, hnR]
    push_cast
    ring
  · intro b
    have := b.2
    rw [lowK_allPos, shape e s ht z hz hb lam' h' hr b]
    by_cases hc : (b : ℕ) < t
    · have h0 : ν (Fin.rev b) = 0 := by
        simp only [ν]
        rw [dif_neg (by simp only [Fin.val_rev]; omega)]
      rw [dif_pos hc, h0]
      push_cast
      rw [htR, hnR]
      ring
    · rw [dif_neg hc, hν _ ⟨b - t, by omega⟩ (by simp only [Fin.val_rev]; omega)]
      simp only
      rw [Nat.cast_sub (by omega)]
      push_cast
      rw [htR, hnR]
      ring

def IsEntry {R : Ranks} (P : HCParam R) (j : ℕ) (y : ℚ) : Prop :=
  (∃ i, y = P.v i) ∨ (∃ i, y = -P.b i) ∨
    ∃ i : Fin R.m, (i : ℕ) < j ∧ ∃ a : ℕ, a < R.t ∧ y = -P.e i + ((R.t : ℚ) - 1) / 2 - a

lemma mem_parB (D : D7) (j : ℕ) (hj : D.R.m ≤ j + 1) (τ : D.what₂.Tau) (q : ℚ) (s : Bool) :
    (q, s) ∈ parB (Ptw D) j τ ↔
      s = true ∧ IsEntry (D.hc τ) j (-q - if Odd j then -(1 / 2) else 0) := by
  have hi : ∀ i : Fin D.R.m, (i : ℕ) ≤ j := fun i => by have := i.2; omega
  simp only [parB, dualPar, TPar.Dpar, TPar.block, Ptw, tparRec, tparHC, Finset.mem_image,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, hi, true_or, decide_true, IsEntry]
  generalize (if Odd j then -(1 / 2) else 0 : ℚ) = c
  constructor
  · rintro ⟨_, ⟨_, (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, hij, _, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩, h⟩ <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> refine ⟨rfl, ?_⟩
    · exact .inl ⟨i, by simp⟩
    · exact .inr (.inl ⟨i, by simp⟩)
    · exact .inr (.inr ⟨i, hij, a, ha, by simp⟩)
  · rintro ⟨rfl, ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, hij, a, ha, h⟩⟩
    · exact ⟨_, ⟨_, .inl (.inl ⟨i, rfl⟩), rfl⟩, Prod.ext (by simp only; linarith) rfl⟩
    · exact ⟨_, ⟨_, .inl (.inr ⟨i, rfl⟩), rfl⟩, Prod.ext (by simp only; linarith) rfl⟩
    · exact ⟨_, ⟨_, .inr ⟨i, hij, _, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩, Prod.ext (by simp only; linarith) rfl⟩

lemma entry_int {R : Ranks} (P : HCParam R) (j : ℕ) (y : ℚ) (h : IsEntry P j y) : ∃ z : ℤ, y = z := by
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, -, a, ha, rfl⟩
  · exact P.v_int i
  · exact GlobalTheory.ForcedWeights.entry_int P (.inr (.inl i))
  · exact GlobalTheory.ForcedWeights.entry_int P (.inr (.inr (i, ⟨a, ha⟩)))

lemma entry_ge {R : Ranks} (P : HCParam R) (k : Fin R.m) (hk : (k : ℕ) + 1 = R.m) (y : ℚ)
    (h : IsEntry P k y) : -P.e k + ((R.t : ℚ) + 3) / 2 ≤ y := by
  have h0 := P.gap_be k
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, hi, a, ha, rfl⟩
  · have := GlobalTheory.ForcedWeights.negb_lt_v P i k
    linarith
  · have := GlobalTheory.ForcedWeights.be P (i := i) (j := k) (by have := i.2; rw [Fin.le_def]; omega)
    linarith
  · have := GlobalTheory.ForcedWeights.eb P (i := i) (j := k) hi
    have ha' : (a : ℚ) + 1 ≤ R.t := by exact_mod_cast ha
    linarith

lemma entry_succ {R : Ranks} (P : HCParam R) (k : Fin R.m) (hk : (k : ℕ) + 1 = R.m) (y : ℚ) :
    IsEntry P R.m y ↔ IsEntry P k y ∨ ∃ a : ℕ, a < R.t ∧ y = -P.e k + ((R.t : ℚ) - 1) / 2 - a := by
  constructor
  · rintro (h | h | ⟨i, -, h⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · by_cases hi : (i : ℕ) < k
      · exact .inl (.inr (.inr ⟨i, hi, h⟩))
      · have : i = k := Fin.ext (by have := i.2; omega)
        subst this
        exact .inr h
  · rintro ((h | h | ⟨i, -, h⟩) | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨i, i.2, h⟩)
    · exact .inr (.inr ⟨k, k.2, h⟩)

theorem lastStep_param : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), (k : ℕ) + 1 = D.R.m → n = D.R.r + k * D.R.t → N = n + D.R.t → IsEnum (parB (Ptw D) k τ) lam ε → IsEnum (parB (Ptw D) D.R.m τ) lam' ε' → ε = allPos n ∧ ε' = allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = expS D k τ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + expT D k τ) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (allPos n) lam a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (allPos N) lam' b = -(x₁ : ℝ) - ν (Fin.rev b) := by
  intro D k τ n N lam ε lam' ε' hk hn hN ⟨hl, q, hq, hS⟩ ⟨hl', q', hq', hS'⟩
  subst hN
  obtain ⟨s, hs⟩ := D.R.t_odd
  obtain ⟨m', hm'⟩ := D.R.m_even
  obtain ⟨k', hk'⟩ := D.R.k_even
  obtain ⟨e, he⟩ := (D.hc τ).e_int k
  have hm2 := D.R.two_le_m
  have hkodd : Odd (k : ℕ) := ⟨m' - 1, by omega⟩
  have hkne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hkodd
  have hmno : ¬ Odd D.R.m := Nat.not_odd_iff_even.mpr D.R.m_even
  have hnev : Even n := by
    rw [hn]
    refine Odd.add_odd ⟨k' + m' - 1, ?_⟩ (hkodd.mul D.R.t_odd)
    unfold Ranks.r; omega
  obtain ⟨p, hp⟩ := hnev
  have hsQ : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hpQ : (n : ℚ) = 2 * p := by rw [hp]; push_cast; ring
  have A : ∀ x b, (∃ a, (q a, ε a) = (x, b)) ↔ b = true ∧ IsEntry (D.hc τ) k (-x + 1 / 2) := by
    intro x b
    have := mem_parB D k (by omega) τ x b
    rw [hS, if_pos hkodd, sub_neg_eq_add] at this
    simpa using this
  have B : ∀ x b, (∃ a, (q' a, ε' a) = (x, b)) ↔ b = true ∧ IsEntry (D.hc τ) D.R.m (-x) := by
    intro x b
    have := mem_parB D D.R.m (by omega) τ x b
    rw [hS', if_neg hmno, sub_zero] at this
    simpa using this
  have hε : ∀ a, ε a = true := fun a => ((A _ _).mp ⟨a, rfl⟩).1
  have hε' : ∀ a, ε' a = true := fun a => ((B _ _).mp ⟨a, rfl⟩).1
  have hE : ∀ a, IsEntry (D.hc τ) k (-q a + 1 / 2) := fun a => ((A _ _).mp ⟨a, rfl⟩).2
  choose z hz using fun a => entry_int _ _ _ (hE a)
  refine ⟨funext hε, funext hε', -e + p, e - p - s, ?_, ?_, ?_⟩
  · simp only [expS, if_neg hkne, he, hpQ]
    push_cast
    ring
  · simp only [expT, if_neg hkne, he]
    push_cast
    rw [hpQ, hsQ]
    ring
  refine partition e s p (by exact_mod_cast hs) (by omega) z lam hl ?_ ?_ lam' hl' ?_
  · intro a
    have : q a = -(z a : ℚ) + 1 / 2 := by linarith [hz a]
    rw [hq, this]
    push_cast
    ring
  · intro a
    have h1 := entry_ge _ k hk _ (hE a)
    rw [hz, he, hsQ] at h1
    have h2 : -(e : ℚ) + s + 2 ≤ z a := by linarith
    exact_mod_cast h2
  · intro x
    constructor
    · rintro ⟨b, rfl⟩
      rcases (entry_succ _ k hk _).mp ((B _ _).mp ⟨b, rfl⟩).2 with h | ⟨a, ha, h⟩
      · obtain ⟨a, ha⟩ := (A (q' b + 1 / 2) true).mpr ⟨rfl, by convert h using 1; ring⟩
        refine .inl ⟨a, ?_⟩
        have h1 : q a = q' b + 1 / 2 := (Prod.mk.inj ha).1
        have h2 : q' b = -(z a : ℚ) := by linarith [hz a]
        rw [hq', h2]
        push_cast
        ring
      · refine .inr ⟨D.R.t - 1 - a, by omega, ?_⟩
        have h2 : q' b = e - s + a := by rw [he, hsQ] at h; linarith
        have h3 : ((D.R.t - 1 - a : ℕ) : ℤ) = 2 * s - a := by omega
        rw [hq', h2, h3]
        push_cast
        ring
    · rintro (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
      · obtain ⟨b, hb⟩ := (B (-(z a : ℚ)) true).mpr
          ⟨rfl, (entry_succ _ k hk _).mpr (.inl (by rw [neg_neg, ← hz]; exact hE a))⟩
        refine ⟨b, ?_⟩
        rw [hq', (Prod.mk.inj hb).1]
        push_cast
        ring
      · have h3 : ((D.R.t - 1 - c : ℕ) : ℚ) = 2 * s - c := by
          have : ((D.R.t - 1 - c : ℕ) : ℤ) = 2 * s - c := by omega
          exact_mod_cast this
        obtain ⟨b, hb⟩ := (B ((e : ℚ) + s - c) true).mpr
          ⟨rfl, (entry_succ _ k hk _).mpr (.inr ⟨D.R.t - 1 - c, by omega, by
            rw [h3, he, hsQ]; ring⟩)⟩
        refine ⟨b, ?_⟩
        rw [hq', (Prod.mk.inj hb).1]
        push_cast
        ring

end GlobalTheory.LastStepParam
