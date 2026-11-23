import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantEqOfNormGe
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.LemmaHG

open GlobalTheory.CompanionTheory.RealCount.LemmaH

theorem abel_le (n : ℕ) (x u v : ℕ → ℝ) (hx : ∀ i, i + 1 < n → x (i + 1) ≤ x i)
    (hD : ∀ j, j ≤ n → ∑ i ∈ Finset.range j, u i ≤ ∑ i ∈ Finset.range j, v i)
    (hT : ∑ i ∈ Finset.range n, u i = ∑ i ∈ Finset.range n, v i) :
    ∑ i ∈ Finset.range n, x i * u i ≤ ∑ i ∈ Finset.range n, x i * v i := by
  rcases n with _ | N
  · simp
  have key : ∀ m, m + 1 ≤ N + 1 →
      x m * (∑ i ∈ Finset.range (m + 1), v i - ∑ i ∈ Finset.range (m + 1), u i) ≤
        ∑ i ∈ Finset.range (m + 1), x i * v i - ∑ i ∈ Finset.range (m + 1), x i * u i := by
    intro m
    induction m with
    | zero => intro _; simp; linarith
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have h1 := hx m (by omega)
      have h2 := hD (m + 1) (by omega)
      rw [Finset.sum_range_succ v (m + 1), Finset.sum_range_succ u (m + 1),
        Finset.sum_range_succ (fun i => x i * v i) (m + 1),
        Finset.sum_range_succ (fun i => x i * u i) (m + 1)]
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  have := key N le_rfl
  rw [hT, sub_self, mul_zero] at this
  linarith

def cnt (S : Finset ℕ) (p j : ℕ) : ℕ := (S.filter fun a => p ≤ a ∧ a < j).card

theorem cnt_add (S : Finset ℕ) {p q j : ℕ} (hpq : p ≤ q) (hqj : q ≤ j) :
    cnt S p q + cnt S q j = cnt S p j := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, h1, h2⟩ | ⟨h, h1, h2⟩)
      · exact ⟨h, h1, by omega⟩
      · exact ⟨h, by omega, h2⟩
    · rintro ⟨h, h1, h2⟩
      by_cases hq : a < q
      · exact Or.inl ⟨h, h1, hq⟩
      · exact Or.inr ⟨h, by omega, h2⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    have := (Finset.mem_filter.1 ha).2
    have := (Finset.mem_filter.1 hb).2
    omega

theorem cnt_le (S : Finset ℕ) {p j : ℕ} (hpj : p ≤ j) : cnt S p j + p ≤ j := by
  have : (S.filter fun a => p ≤ a ∧ a < j) ⊆ Finset.Ico p j := by
    intro a ha
    have := (Finset.mem_filter.1 ha).2
    exact Finset.mem_Ico.2 this
  have := Finset.card_le_card this
  simp only [Nat.card_Ico] at this
  unfold cnt
  omega

theorem sum_shift_nat (t : ℕ) (p : ℝ) :
    2 * ∑ i ∈ Finset.range t, (p + (i : ℝ)) = t * (2 * p + t - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem piece_le (A : Finset ℕ) (p q : ℕ) (hA : ∀ a ∈ A, a < q) :
    ∑ a ∈ A, (a : ℝ) + ∑ i ∈ Finset.range A.card, ((p : ℝ) + i) ≤ A.card * ((p : ℝ) + q - 1) := by
  have h1 := sum_le_top A q hA
  have h2 := sum_shift_nat A.card p
  nlinarith

theorem maj (S : Finset ℕ) (n : ℕ) : ∀ m p, p + m = n → ∃ c : ℕ → ℝ,
    (∀ a, p ≤ a → a < n → 0 ≤ c a) ∧
    (∀ a b, p ≤ a → a ≤ b → b < n → c b ≤ c a) ∧
    (∀ j, p ≤ j → j ≤ n → (cnt S p j : ℝ) ≤ ∑ i ∈ Finset.Ico p j, c i) ∧
    (∑ i ∈ Finset.Ico p n, c i = cnt S p n) ∧
    (∀ f : ℝ, (∀ j, p < j → j ≤ n → (cnt S p j : ℝ) ≤ f * ((j : ℝ) - p)) → ∀ a, p ≤ a → a < n → c a ≤ f) ∧
    (∑ a ∈ S.filter (fun a => p ≤ a ∧ a < n), (a : ℝ) + ∑ i ∈ Finset.range (cnt S p n), ((p : ℝ) + i) ≤
      2 * ∑ i ∈ Finset.Ico p n, (i : ℝ) * c i) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p hpm
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hpn : p = n := by omega
    subst hpn
    have hemp : S.filter (fun a => p ≤ a ∧ a < p) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      omega
    refine ⟨fun _ => 0, fun _ _ _ => le_rfl, fun _ _ _ _ _ => le_rfl, ?_, ?_, ?_, ?_⟩
    · intro j h1 h2
      have : j = p := by omega
      subst this
      simp [cnt, hemp]
    · simp [cnt, hemp]
    · intro f _ a h1 h2
      omega
    · simp [cnt, hemp]

  have hne : (Finset.Ioc p n).Nonempty := ⟨n, Finset.mem_Ioc.2 ⟨by omega, le_rfl⟩⟩
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image (Finset.Ioc p n)
    (fun j => (cnt S p j : ℝ) / ((j : ℝ) - p)) hne
  obtain ⟨hpq, hqn⟩ := Finset.mem_Ioc.1 hq
  have hd : (0 : ℝ) < (q : ℝ) - p := by
    have : (p : ℝ) < q := by exact_mod_cast hpq
    linarith
  set f0 : ℝ := (cnt S p q : ℝ) / ((q : ℝ) - p) with hf0
  have hf0n : 0 ≤ f0 := div_nonneg (Nat.cast_nonneg _) hd.le
  have hf0q : f0 * ((q : ℝ) - p) = cnt S p q := div_mul_cancel₀ _ hd.ne'
  have hslope : ∀ j, p < j → j ≤ n → (cnt S p j : ℝ) ≤ f0 * ((j : ℝ) - p) := by
    intro j h1 h2
    have hdj : (0 : ℝ) < (j : ℝ) - p := by
      have : (p : ℝ) < j := by exact_mod_cast h1
      linarith
    have := hmax j (Finset.mem_Ioc.2 ⟨h1, h2⟩)
    exact (div_le_iff₀ hdj).1 this
  obtain ⟨c', i0, i1, i2, i3, i4, i5⟩ := ih (n - q) (by omega) q (by omega)
  have hcq : ∀ j, q ≤ j → (cnt S p j : ℝ) = cnt S p q + cnt S q j := by
    intro j hj
    rw [← cnt_add S hpq.le hj]
    push_cast
    ring
  have hrest : ∀ a, q ≤ a → a < n → c' a ≤ f0 := by
    refine i4 f0 fun j h1 h2 => ?_
    have h3 := hslope j (by omega) h2
    rw [hcq j h1.le, ← hf0q] at h3
    linarith
  have hc0 : ∀ i ∈ Finset.Ico p q, (if i < q then f0 else c' i) = f0 := fun i hi =>
    if_pos (Finset.mem_Ico.1 hi).2
  have hc1 : ∀ i ∈ Finset.Ico q n, (if i < q then f0 else c' i) = c' i := fun i hi =>
    if_neg (by have := (Finset.mem_Ico.1 hi).1; omega)
  have hsplit : ∀ (g : ℕ → ℝ) j, q ≤ j → ∑ i ∈ Finset.Ico p j, g i =
      ∑ i ∈ Finset.Ico p q, g i + ∑ i ∈ Finset.Ico q j, g i := fun g j hj =>
    (Finset.sum_Ico_consecutive g hpq.le hj).symm
  have hsum0 : ∀ j, p ≤ j → j ≤ q → ∑ i ∈ Finset.Ico p j, (if i < q then f0 else c' i) =
      f0 * ((j : ℝ) - p) := by
    intro j h1 h2
    rw [Finset.sum_congr rfl (fun i hi => if_pos (lt_of_lt_of_le (Finset.mem_Ico.1 hi).2 h2))]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [Nat.cast_sub h1]
    ring
  have hsum1 : ∀ j, q ≤ j → j ≤ n → ∑ i ∈ Finset.Ico q j, (if i < q then f0 else c' i) =
      ∑ i ∈ Finset.Ico q j, c' i := by
    intro j h1 h2
    exact Finset.sum_congr rfl fun i hi => if_neg (by have := (Finset.mem_Ico.1 hi).1; omega)
  refine ⟨fun a => if a < q then f0 else c' a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a h1 h2
    by_cases h : a < q
    · simpa only [if_pos h] using hf0n
    · simpa only [if_neg h] using i0 a (by omega) h2
  · intro a b h1 h2 h3
    by_cases ha : a < q
    · by_cases hb : b < q
      · simp only [if_pos ha, if_pos hb, le_refl]
      · simp only [if_pos ha, if_neg hb]
        exact hrest b (by omega) h3
    · have hb : ¬ b < q := by omega
      simp only [if_neg ha, if_neg hb]
      exact i1 a b (by omega) h2 h3
  · intro j h1 h2
    by_cases hj : j ≤ q
    · rw [hsum0 j h1 hj]
      rcases Nat.eq_or_lt_of_le h1 with rfl | h3
      · have : cnt S p p = 0 := by
          have := cnt_le S (le_refl p)
          omega
        simp [this]
      · exact hslope j h3 h2
    · have hj' : q ≤ j := by omega
      rw [hsplit _ j hj', hsum0 q hpq.le le_rfl, hsum1 j hj' h2, hcq j hj', hf0q]
      have := i2 j hj' h2
      linarith
  · rw [hsplit _ n hqn, hsum0 q hpq.le le_rfl, hsum1 n hqn le_rfl, hcq n hqn, hf0q, i3]
  · intro f hf a h1 h2
    have hfq : f0 ≤ f := by
      have := hf q hpq hqn
      exact (div_le_iff₀ hd).2 this
    by_cases h : a < q
    · simpa only [if_pos h] using hfq
    · simpa only [if_neg h] using (hrest a (by omega) h2).trans hfq
  ·
    set A := S.filter (fun a => p ≤ a ∧ a < q) with hA
    set B := S.filter (fun a => q ≤ a ∧ a < n) with hB
    have hAB : S.filter (fun a => p ≤ a ∧ a < n) = A ∪ B := by
      ext a
      simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨h, h1, h2⟩
        by_cases hq' : a < q
        · exact Or.inl ⟨h, h1, hq'⟩
        · exact Or.inr ⟨h, by omega, h2⟩
      · rintro (⟨h, h1, h2⟩ | ⟨h, h1, h2⟩)
        · exact ⟨h, h1, by omega⟩
        · exact ⟨h, by omega, h2⟩
    have hdis : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have := (Finset.mem_filter.1 ha).2
      have := (Finset.mem_filter.1 hb).2
      omega
    have hcA : A.card = cnt S p q := rfl
    have hcn : cnt S p n = cnt S p q + cnt S q n := (cnt_add S hpq.le hqn).symm
    have hcle := cnt_le S hpq.le
    have hp := piece_le A p q (fun a ha => (Finset.mem_filter.1 ha).2.2)
    rw [hcA] at hp
    rw [hAB, Finset.sum_union hdis, hcn, Finset.sum_range_add]
    have hsh : ∑ i ∈ Finset.range (cnt S q n), ((p : ℝ) + ((cnt S p q + i : ℕ) : ℝ)) ≤
        ∑ i ∈ Finset.range (cnt S q n), ((q : ℝ) + i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have : ((cnt S p q + p : ℕ) : ℝ) ≤ q := by exact_mod_cast hcle
      push_cast at this ⊢
      linarith
    have hI : 2 * ∑ i ∈ Finset.Ico p q, (i : ℝ) * (if i < q then f0 else c' i) =
        (cnt S p q : ℝ) * ((p : ℝ) + q - 1) := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [hc0 i hi]), ← Finset.sum_mul]
      obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
      have h2 := two_sum_Ico p d
      rw [← hf0q]
      push_cast at h2 ⊢
      nlinarith [h2]
    have hJ : ∑ i ∈ Finset.Ico q n, (i : ℝ) * (if i < q then f0 else c' i) =
        ∑ i ∈ Finset.Ico q n, (i : ℝ) * c' i :=
      Finset.sum_congr rfl fun i hi => by rw [hc1 i hi]
    rw [hsplit _ n hqn, mul_add, hI, hJ]
    linarith

theorem dom_sum (n : ℕ) (ν L : ℕ → ℝ) (C : ℝ) (hν : ∀ i, i + 1 < n → ν (i + 1) ≤ ν i)
    (hL : ∀ i, i + 1 < n → L (i + 1) ≤ L i)
    (hP : ∀ j, j ≤ n → ∑ i ∈ Finset.range j, ν i ≤ ∑ i ∈ Finset.range j, (L i + C - 2 * (i : ℝ)))
    (hT : ∑ i ∈ Finset.range n, ν i = ∑ i ∈ Finset.range n, (L i + C - 2 * (i : ℝ)))
    (I : Finset ℕ) (hI : ∀ i ∈ I, i < n) :
    ∑ i ∈ I, (ν i + (i : ℝ)) ≤ ∑ i ∈ Finset.range I.card, (L i + C - 2 * (i : ℝ) + (i : ℝ)) := by
  classical
  obtain ⟨c, c0, c1, c2, c3, c4, c5⟩ := maj I n n 0 (by omega)
  simp only [← Finset.range_eq_Ico] at c2 c3 c5
  have hfil : ∀ j, j ≤ n → ∑ i ∈ Finset.range j, (if i ∈ I then (1 : ℝ) else 0) = cnt I 0 j := by
    intro j _
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one, cnt]
    congr 2
    ext a
    simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Nat.zero_le _, h1⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h2, h1⟩
  have hsub : I ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hI i hi)
  have hfilI : I.filter (fun a => 0 ≤ a ∧ a < n) = I := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, Nat.zero_le _, hI a h⟩⟩
  have hcard : cnt I 0 n = I.card := by rw [cnt, hfilI]
  rw [hfilI, hcard] at c5
  rw [hcard] at c3
  set k := I.card with hk
  have hkn : k ≤ n := by simpa using Finset.card_le_card hsub
  have hc1 : ∀ a, a < n → c a ≤ 1 := by
    intro a ha
    refine c4 1 (fun j h1 h2 => ?_) a (Nat.zero_le _) ha
    have := cnt_le I (Nat.zero_le j)
    have h3 : (cnt I 0 j : ℝ) ≤ j := by exact_mod_cast (by omega : cnt I 0 j ≤ j)
    simpa using h3

  have a1 := abel_le n ν (fun i => if i ∈ I then 1 else 0) c hν
    (fun j hj => by
      rw [hfil j hj]
      exact c2 j (Nat.zero_le _) hj)
    (by rw [hfil n le_rfl, hcard, c3])
  have a2 := abel_le n c ν (fun i => L i + C - 2 * (i : ℝ))
    (fun i hi => c1 i (i + 1) (Nat.zero_le _) (by omega) hi) hP hT
  have hv : ∀ j, ∑ i ∈ Finset.range j, (if i < k then (1 : ℝ) else 0) = min j k := by
    intro j
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.range j).filter (fun i => i < k) = Finset.range (min j k) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [this, Finset.card_range]
  have a3 := abel_le n L c (fun i => if i < k then 1 else 0) hL
    (fun j hj => by
      rw [hv j, Nat.cast_min]
      refine le_min ?_ ?_
      · have := Finset.sum_le_card_nsmul (Finset.range j) c 1
          (fun i hi => hc1 i (by have := Finset.mem_range.1 hi; omega))
        simpa using this
      · rw [← c3]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega))
          (fun i hi _ => c0 i (Nat.zero_le _) (Finset.mem_range.1 hi)))
    (by rw [hv n, c3, min_eq_right hkn])
  have e1 : ∑ i ∈ Finset.range n, ν i * (if i ∈ I then (1 : ℝ) else 0) = ∑ i ∈ I, ν i := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  have e2 : ∑ i ∈ Finset.range n, L i * (if i < k then (1 : ℝ) else 0) =
      ∑ i ∈ Finset.range k, L i := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have e3 : ∑ i ∈ Finset.range n, c i * (L i + C - 2 * (i : ℝ)) =
      ∑ i ∈ Finset.range n, L i * c i + C * k - 2 * ∑ i ∈ Finset.range n, (i : ℝ) * c i := by
    rw [← c3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i ∈ Finset.range n, ν i * c i = ∑ i ∈ Finset.range n, c i * ν i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e5 : ∑ i ∈ Finset.range k, (L i + C - 2 * (i : ℝ) + (i : ℝ)) =
      ∑ i ∈ Finset.range k, L i + C * k - ∑ i ∈ Finset.range k, (0 + (i : ℝ)) := by
    have : C * k = ∑ i ∈ Finset.range k, C := by simp [mul_comm]
    rw [this, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1] at a1
  rw [e2] at a3
  rw [e3] at a2
  rw [e4] at a1
  rw [Finset.sum_add_distrib, e5]
  push_cast at c5
  linarith

variable {n : ℕ}

theorem lam_step (lam : Fin n → ℤ) (hl : Antitone lam) (i : ℕ) (h : i + 1 < n) :
    ex (fun a => 2 * (lam a : ℝ)) (i + 1) ≤ ex (fun a => 2 * (lam a : ℝ)) i := by
  rw [ex_mk _ h, ex_mk _ (show i < n by omega)]
  have := hl (show (⟨i, by omega⟩ : Fin n) ≤ ⟨i + 1, h⟩ from Fin.mk_le_mk.2 (by omega))
  have h2 : ((lam ⟨i + 1, h⟩ : ℤ) : ℝ) ≤ ((lam ⟨i, by omega⟩ : ℤ) : ℝ) := by exact_mod_cast this
  linarith

theorem step1 (lam : Fin n → ℤ) (hl : Antitone lam) (ν : Fin n → ℤ) (hν : Antitone ν)
    (hD : DomLE (wtR ν) (m0 lam)) (w : Equiv.Perm (Fin n)) {k : ℕ} (hk : k ≤ n) :
    ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), (wtR ν (w a) - rhoV n (w a)) ≤
      ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), (m0 lam a - rhoV n a) := by
  classical
  set F := univ.filter (fun a : Fin n => (a : ℕ) < k) with hF
  set Lf : Fin n → ℝ := fun a => 2 * (lam a : ℝ) with hLf
  set I : Finset ℕ := (F.map w.toEmbedding).map Fin.valEmbedding with hIdef
  have hM : ∀ a : Fin n, ex Lf (a : ℕ) + ((n : ℝ) - 1) - 2 * ((a : ℕ) : ℝ) = m0 lam a := by
    intro a
    rw [ex_val]
    simp only [hLf, m0]
  have hcard : I.card = k := by simp [hIdef, hF, card_filter_lt hk]
  have hcore := dom_sum n (ex (wtR ν)) (ex Lf) ((n : ℝ) - 1)
    (by
      intro i h
      rw [ex_mk _ h, ex_mk _ (show i < n by omega)]
      have := hν (show (⟨i, by omega⟩ : Fin n) ≤ ⟨i + 1, h⟩ from Fin.mk_le_mk.2 (by omega))
      simp only [wtR]
      exact_mod_cast this)
    (lam_step lam hl)
    (by
      intro j hj
      rw [sum_range_of (wtR ν) _ hj (fun a => ex_val _ a), sum_range_of (m0 lam) (fun i : ℕ => ex Lf i + ((n : ℝ) - 1) - 2 * (i : ℝ)) hj hM]
      exact hD.1 j)
    (by
      have h1 := sum_range_of (wtR ν) _ (le_refl n) (fun a => ex_val _ a)
      have h2 := sum_range_of (m0 lam) (fun i : ℕ => ex Lf i + ((n : ℝ) - 1) - 2 * (i : ℝ)) (le_refl n) hM
      have h3 : univ.filter (fun a : Fin n => (a : ℕ) < n) = univ :=
        Finset.filter_true_of_mem fun a _ => a.2
      rw [h1, h2, h3]
      exact hD.2)
    I
    (by
      intro i hi
      simp only [hIdef, Finset.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2)
  rw [hcard] at hcore
  have hL : ∑ i ∈ I, (ex (wtR ν) i + (i : ℝ)) = ∑ a ∈ F, (wtR ν (w a) + ((w a : ℕ) : ℝ)) := by
    simp only [hIdef, Finset.sum_map, Equiv.coe_toEmbedding, Fin.valEmbedding_apply, ex_val]
  have hR : ∑ i ∈ Finset.range k, (ex Lf i + ((n : ℝ) - 1) - 2 * (i : ℝ) + (i : ℝ)) =
      ∑ a ∈ F, (m0 lam a + ((a : ℕ) : ℝ)) :=
    sum_range_of (fun a => m0 lam a + ((a : ℕ) : ℝ)) _ hk
      (fun a => by rw [← hM a])
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

theorem ivt (f : ℕ → ℤ) (c : ℕ) (t : ℤ) (h1 : t ≤ f c) : ∀ d, c ≤ d →
    (∀ i, c ≤ i → i < d → f i - 1 ≤ f (i + 1)) → f d ≤ t → ∃ i, c ≤ i ∧ i ≤ d ∧ f i = t := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro _ h2
    exact ⟨c, le_rfl, le_rfl, le_antisymm h2 h1⟩
  | succ d hd ih =>
    intro hs h2
    rcases eq_or_lt_of_le h2 with h3 | h3
    · exact ⟨d + 1, by omega, le_rfl, h3⟩
    · have h4 := hs d hd (by omega)
      obtain ⟨i, a, b, e⟩ := ih (fun i p q => hs i p (by omega)) (by omega)
      exact ⟨i, a, by omega, e⟩

theorem sep (n : ℕ) (f : ℕ → ℕ) (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (H : ∀ i, i + 1 < n → f i < f (i + 1) ∨ f (i + 1) + 1 = f i)
    (b : ℕ) (hb : b + 1 < n) (hasc : f b < f (b + 1)) (c d : ℕ) (hc : c ≤ b) (hd : b + 1 ≤ d)
    (hdn : d < n) : f c < f d := by
  by_contra hcon
  have hne : f c ≠ f d := fun e => by
    have := hinj c d (by omega) hdn e
    omega
  have hlt : f d < f c := by omega
  have step : ∀ i, i + 1 < n → (f i : ℤ) - 1 ≤ (f (i + 1) : ℤ) := by
    intro i hi
    rcases H i hi with h | h <;> omega
  rcases le_or_gt (f (b + 1)) (f d) with h1 | h1
  · obtain ⟨i, a, b', e⟩ := ivt (fun i => (f i : ℤ)) c (f (b + 1)) (by omega) b hc
      (fun i _ h => step i (by omega)) (by omega)
    have := hinj i (b + 1) (by omega) hb (by simpa using e)
    omega
  · rcases le_or_gt (f d) (f b) with h2 | h2
    · obtain ⟨i, a, b', e⟩ := ivt (fun i => (f i : ℤ)) (b + 1) (f b) (by omega) d hd
        (fun i _ h => step i (by omega)) (by omega)
      have := hinj i b (by omega) (by omega) (by simpa using e)
      omega
    · obtain ⟨i, a, b', e⟩ := ivt (fun i => (f i : ℤ)) c (f d) (by omega) b hc
        (fun i _ h => step i (by omega)) (by omega)
      have := hinj i d (by omega) hdn (by simpa using e)
      omega

theorem cut (n : ℕ) (f : ℕ → ℕ) (hf : ∀ i, i < n → f i < n)
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (H : ∀ i, i + 1 < n → f i < f (i + 1) ∨ f (i + 1) + 1 = f i)
    (b : ℕ) (hb : b + 1 < n) (hasc : f b < f (b + 1)) :
    (∀ c, c ≤ b → f c < b + 1) ∧ (∀ d, b + 1 ≤ d → d < n → b + 1 ≤ f d) := by
  have hs := sep n f hinj H b hb hasc
  constructor
  · intro c hc
    have hsub : (Finset.Ico (b + 1) n).image f ⊆ Finset.Ico (f c + 1) n := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hd
      exact Finset.mem_Ico.2 ⟨hs c d hc h1 h2, hf d h2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn (fun i hi j hj e =>
      hinj i j (Finset.mem_Ico.1 hi).2 (Finset.mem_Ico.1 hj).2 e)] at h1
    simp only [Nat.card_Ico] at h1
    have := hf c (by omega)
    omega
  · intro d h1 h2
    have hsub : (Finset.range (b + 1)).image f ⊆ Finset.range (f d) := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hs c d (by have := Finset.mem_range.1 hc; omega) h1 h2)
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn (fun i hi j hj e =>
      hinj i j (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hj; omega) e)] at h3
    simpa using h3

theorem T_mono (n : ℕ) (f : ℕ → ℕ) (H : ∀ i, i + 1 < n → f i < f (i + 1) ∨ f (i + 1) + 1 = f i)
    (i j : ℕ) (hij : i ≤ j) : j < n → f i + i ≤ f j + j := by
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hj ih =>
    intro hn
    have := ih (by omega)
    rcases H j hn with h | h <;> omega

theorem blocks (n : ℕ) (f : ℕ → ℕ) (hf : ∀ i, i < n → f i < n)
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (H : ∀ i, i + 1 < n → f i < f (i + 1) ∨ f (i + 1) + 1 = f i) (b : ℕ) (hb : b < n) :
    ∃ p q, p ≤ b ∧ b < q ∧ q ≤ n ∧ (∀ c, c < n → (c < p ↔ f c + c < f b + b)) ∧
      (∀ c, c < n → (c < q ↔ f c + c ≤ f b + b)) ∧ f b + b + 1 = p + q := by
  classical
  have hm := T_mono n f H
  have hex1 : ∃ c, f b + b ≤ f c + c := ⟨b, le_rfl⟩
  have hex2 : ∃ c, c = n ∨ f b + b < f c + c := ⟨n, Or.inl rfl⟩
  obtain ⟨p, hp1, hp2, hpb⟩ : ∃ p, f b + b ≤ f p + p ∧ (∀ c, c < p → f c + c < f b + b) ∧ p ≤ b :=
    ⟨Nat.find hex1, Nat.find_spec hex1, fun c hc => not_le.1 (Nat.find_min hex1 hc),
      Nat.find_min' hex1 le_rfl⟩
  obtain ⟨q, hq1, hq2, hqn⟩ : ∃ q, (q = n ∨ f b + b < f q + q) ∧
      (∀ c, c < q → c ≠ n ∧ f c + c ≤ f b + b) ∧ q ≤ n :=
    ⟨Nat.find hex2, Nat.find_spec hex2, fun c hc => by
      have := Nat.find_min hex2 hc
      push_neg at this
      exact this, Nat.find_min' hex2 (Or.inl rfl)⟩
  have hbq : b < q := by
    by_contra hcon
    rcases hq1 with h | h
    · omega
    · have := hm q b (by omega) hb
      omega
  have chp : ∀ c, c < n → (c < p ↔ f c + c < f b + b) := by
    intro c hc
    refine ⟨hp2 c, fun h => ?_⟩
    by_contra hcon
    have := hm p c (by omega) hc
    omega
  have chq : ∀ c, c < n → (c < q ↔ f c + c ≤ f b + b) := by
    intro c hc
    refine ⟨fun h => (hq2 c h).2, fun h => ?_⟩
    by_contra hcon
    rcases hq1 with h1 | h1
    · omega
    · have := hm q c (by omega) hc
      omega
  refine ⟨p, q, hpb, hbq, hqn, chp, chq, ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hTp : f p + p = f b + b := le_antisymm ((chq p (by omega)).1 (by omega)) hp1
  have hTq : f r + r = f b + b :=
    le_antisymm ((chq _ (by omega)).1 (by omega)) (hm b r (by omega) (by omega))
  have hup : f p < r + 1 := by
    by_cases hqn' : r + 1 < n
    · have h1 : f b + b < f (r + 1) + (r + 1) := by
        rcases hq1 with h1 | h1
        · omega
        · exact h1
      have hasc : f r < f (r + 1) := by
        rcases H r hqn' with h | h <;> omega
      exact (cut n f hf hinj H r hqn' hasc).1 p (by omega)
    · have : r + 1 = n := by omega
      rw [this]
      exact hf p (by omega)
  have hlo : p ≤ f r := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · omega
    · obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
      have h1 := hp2 s (by omega)
      have hsn : s + 1 < n := by omega
      have hasc : f s < f (s + 1) := by
        rcases H s hsn with h | h <;> omega
      exact (cut n f hf hinj H s hsn hasc).2 r (by omega) (by omega)
  omega

theorem harm_of_perm (lam : Fin n → ℤ) (hl : Antitone lam) (ν : Fin n → ℤ) (hν : Antitone ν)
    (π : Equiv.Perm (Fin n))
    (h : ∀ b, ν b = 2 * lam (π b) + ((n : ℤ) - 1) - ((π b : ℕ) : ℤ) - ((b : ℕ) : ℤ)) :
    ν ∈ harmZ lam := by
  classical
  set f : ℕ → ℕ := fun i => if h : i < n then (π ⟨i, h⟩ : ℕ) else 0 with hfdef
  set g : ℕ → ℤ := fun i => if h : i < n then lam (π ⟨i, h⟩) else 0 with hgdef
  have hfv : ∀ a : Fin n, f a = π a := fun a => by simp only [hfdef, dif_pos a.2]
  have hgv : ∀ a : Fin n, g a = lam (π a) := fun a => by simp only [hgdef, dif_pos a.2]
  have hfn : ∀ i, i < n → f i < n := fun i hi => by
    have := hfv ⟨i, hi⟩
    simp only at this
    rw [this]
    exact (π ⟨i, hi⟩).2
  have hinj : ∀ i j, i < n → j < n → f i = f j → i = j := by
    intro i j hi hj e
    have h1 := hfv ⟨i, hi⟩
    have h2 := hfv ⟨j, hj⟩
    simp only at h1 h2
    rw [h1, h2] at e
    have := π.injective (Fin.ext e)
    exact congrArg Fin.val this
  have H : ∀ i, i + 1 < n → f i < f (i + 1) ∨ (f (i + 1) + 1 = f i ∧ g i = g (i + 1)) := by
    intro i hi
    have h1 : ν ⟨i + 1, hi⟩ ≤ ν ⟨i, by omega⟩ := hν (Fin.mk_le_mk.2 (by omega))
    rw [h ⟨i, by omega⟩, h ⟨i + 1, hi⟩] at h1
    have e1 := hfv ⟨i, by omega⟩
    have e2 := hfv ⟨i + 1, hi⟩
    have e3 := hgv ⟨i, by omega⟩
    have e4 := hgv ⟨i + 1, hi⟩
    simp only at e1 e2 e3 e4 h1
    rw [e1, e2, e3, e4]
    set x := π ⟨i, by omega⟩ with hx
    set y := π ⟨i + 1, hi⟩ with hy
    by_cases hlt : (x : ℕ) < y
    · exact Or.inl hlt
    · right
      have hne : x ≠ y := fun e => by
        have := π.injective e
        have := congrArg Fin.val this
        simp only at this
        omega
      have hne' : (x : ℕ) ≠ y := fun e => hne (Fin.ext e)
      have hyx : y ≤ x := Fin.le_def.2 (by omega)
      have hlam := hl hyx
      push_cast at h1
      omega
  have H1 : ∀ i, i + 1 < n → f i < f (i + 1) ∨ f (i + 1) + 1 = f i :=
    fun i hi => (H i hi).imp id And.left
  have hm := T_mono n f H1
  have gconst : ∀ c d, c ≤ d → d < n → f c + c = f d + d → g c = g d := by
    intro c d hcd
    induction d, hcd using Nat.le_induction with
    | base => intro _ _; rfl
    | succ d hd ih =>
      intro hdn e
      have m1 := hm c d hd (by omega)
      have m2 := hm d (d + 1) (by omega) hdn
      rcases H d hdn with h1 | ⟨h1, h2⟩
      · omega
      · rw [ih (by omega) (by omega), h2]
  have hlam : ∀ b : Fin n, lam (π b) = lam b := by
    intro b
    obtain ⟨p, q, h1, h2, h3, chp, chq, hs⟩ := blocks n f hfn hinj H1 b b.2
    have hb := hfv b
    have hpb := hfv (π b)
    have hlow := (chp (f b) (hfn b b.2))
    have hhigh := (chq (f b) (hfn b b.2)).1 (by omega)
    have hT : f (f b) + f b = f b + b := by
      have : ¬ f (f b) + f b < f b + b := fun hc => by
        have := hlow.2 hc
        omega
      omega
    have hff : f (f b) = b := by omega
    rw [hb] at hff
    rw [hpb] at hff
    have hpp : π (π b) = b := Fin.ext hff
    have hg1 := hgv b
    have hg2 := hgv (π b)
    rw [hpp] at hg2
    rw [← hg1, ← hg2]
    have e : ((π b : Fin n) : ℕ) = f b := hb.symm
    rw [e]
    rcases le_total (b : ℕ) (f b) with h4 | h4
    · exact gconst b (f b) h4 (hfn b b.2) hT.symm
    · exact (gconst (f b) b h4 b.2 hT).symm
  have hcl : ∀ b : Fin n, (univ.filter fun c : Fin n => f c + c < f b + b).card < n := by
    intro b
    have := Finset.card_lt_univ_of_notMem (s := univ.filter fun c : Fin n => f c + c < f b + b) (x := b)
      (by simp)
    simpa using this
  set lev : Fin n → Fin n := fun b => ⟨_, hcl b⟩ with hlev
  have hlevlt : ∀ a b : Fin n, (lev a : ℕ) < lev b ↔ f a + a < f b + b := by
    intro a b
    constructor
    · intro h1
      by_contra hc
      have hsub : (univ.filter fun c : Fin n => f c + c < f b + b) ⊆
          (univ.filter fun c : Fin n => f c + c < f a + a) := by
        intro c hc'
        have := (Finset.mem_filter.1 hc').2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩
      have := Finset.card_le_card hsub
      simp only [hlev] at h1
      omega
    · intro h1
      show (univ.filter fun c : Fin n => f c + c < f a + a).card <
        (univ.filter fun c : Fin n => f c + c < f b + b).card
      refine Finset.card_lt_card ⟨fun c hc' => ?_, fun hsub => ?_⟩
      · have := (Finset.mem_filter.1 hc').2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩
      · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ a, h1⟩)
        have := (Finset.mem_filter.1 this).2
        omega
  have hIs : IsLev lam (fun a => (lev a : ℕ)) := by
    refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
    · by_contra hc
      have h1 := (hlevlt b a).1 (by simpa using hc)
      have := hm a b hab b.2
      omega
    · have h1 : ¬ f a + a < f b + b := fun hc => by
        have := (hlevlt a b).2 hc
        simp only at hab
        omega
      have h2 : ¬ f b + b < f a + a := fun hc => by
        have := (hlevlt b a).2 hc
        simp only at hab
        omega
      have h3 : f a + a = f b + b := by omega
      rw [← hlam a, ← hlam b, ← hgv a, ← hgv b]
      rcases le_total (a : ℕ) b with h4 | h4
      · exact gconst a b h4 b.2 h3
      · exact (gconst b a h4 a.2 h3.symm).symm
  simp only [harmZ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨lev, hIs, ?_⟩
  funext b
  obtain ⟨p, q, h1, h2, h3, chp, chq, hs⟩ := blocks n f hfn hinj H1 b b.2
  have c1 : (univ.filter fun c : Fin n => (lev c : ℕ) < lev b).card = p := by
    rw [← card_filter_lt (show p ≤ n by omega)]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hlevlt c b, chp c c.2]
  have c2 : (univ.filter fun c : Fin n => (lev b : ℕ) < lev c).card + q = n := by
    have h4 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun c : Fin n => (c : ℕ) < q)
    rw [card_filter_lt h3] at h4
    have h5 : (univ.filter fun c : Fin n => (lev b : ℕ) < lev c) =
        univ.filter fun c : Fin n => ¬ (c : ℕ) < q := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hlevlt b c, chq c c.2]
      omega
    rw [h5]
    simp only [Finset.card_univ, Fintype.card_fin] at h4
    omega
  simp only [muZ]
  rw [c1, h b, hlam b, ← hfv b]
  have c3 : ((univ.filter fun c : Fin n => (lev b : ℕ) < lev c).card : ℤ) = (n : ℤ) - q := by omega
  rw [c3]
  omega

end GlobalTheory.CompanionTheory.RealCountG.LemmaHG

namespace GlobalTheory.CompanionTheory.RealCountG

open GlobalTheory.CompanionTheory.RealCount.LemmaH GlobalTheory.CompanionTheory.RealCountG.LemmaHG in

theorem mem_harmZ_of_norm_ge {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (ν : Fin n → ℤ)
    (hν : Antitone ν) (hD : DomLE (wtR ν) (m0 lam)) (w : Equiv.Perm (Fin n))
    (hw : Antitone (fun a => wtR ν (w a) - rhoV n (w a)))
    (hn : ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (wtR ν (w a) - rhoV n (w a) + rhoV n a) ^ 2) :
    ν ∈ harmZ lam := by
  rcases n with _ | N
  · exact harm_of_perm lam hl ν hν 1 (fun b => b.elim0)
  set y : Fin (N + 1) → ℝ := fun a => wtR ν (w a) - rhoV (N + 1) (w a) + rhoV (N + 1) a with hy
  have hfull : ∀ (f : Fin (N + 1) → ℝ), ∑ i ∈ Finset.range (N + 1), ex f i = ∑ a, f a := by
    intro f
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun a _ => ex_val f a
  have hsq : ∀ (f : Fin (N + 1) → ℝ), ∑ i ∈ Finset.range (N + 1), (ex f i) ^ 2 = ∑ a, (f a) ^ 2 := by
    intro f
    rw [← Fin.sum_univ_eq_sum_range (fun i => (ex f i) ^ 2)]
    exact Finset.sum_congr rfl fun a _ => by rw [ex_val]
  have hmain := eq_of_dom N (ex (m0 lam)) (ex y)
    (by
      intro i hi
      have hi1 : i + 1 < N + 1 := by omega
      have hi0 : i < N + 1 := by omega
      rw [ex_mk _ hi0, ex_mk _ hi0, ex_mk _ hi1, ex_mk _ hi1]
      have hlt : (⟨i, hi0⟩ : Fin (N + 1)) < ⟨i + 1, hi1⟩ := Fin.mk_lt_mk.2 (by omega)
      have h1 : lam ⟨i + 1, hi1⟩ ≤ lam ⟨i, hi0⟩ := hl hlt.le
      have h2 : ((lam ⟨i + 1, hi1⟩ : ℤ) : ℝ) ≤ ((lam ⟨i, hi0⟩ : ℤ) : ℝ) := by exact_mod_cast h1
      have h3 := hw hlt.le
      simp only [hy, m0, rhoV] at h3 ⊢
      push_cast at h3 ⊢
      linarith)
    (by
      intro j hj
      rw [sum_range_of y _ hj (fun a => ex_val _ a), sum_range_of (m0 lam) _ hj (fun a => ex_val _ a)]
      have h := LemmaHG.step1 lam hl ν hν hD w hj
      have e1 : ∑ a ∈ univ.filter (fun a : Fin (N + 1) => (a : ℕ) < j), y a =
          ∑ a ∈ univ.filter (fun a : Fin (N + 1) => (a : ℕ) < j), (wtR ν (w a) - rhoV (N + 1) (w a)) +
            ∑ a ∈ univ.filter (fun a : Fin (N + 1) => (a : ℕ) < j), rhoV (N + 1) a :=
        Finset.sum_add_distrib
      have e2 : ∑ a ∈ univ.filter (fun a : Fin (N + 1) => (a : ℕ) < j), m0 lam a =
          ∑ a ∈ univ.filter (fun a : Fin (N + 1) => (a : ℕ) < j), (m0 lam a - rhoV (N + 1) a) +
            ∑ a ∈ univ.filter (fun a : Fin (N + 1) => (a : ℕ) < j), rhoV (N + 1) a := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [e1, e2]
      linarith)
    (by
      rw [hfull, hfull]
      have e1 : ∑ a, y a = ∑ a, wtR ν (w a) - ∑ a, rhoV (N + 1) (w a) + ∑ a, rhoV (N + 1) a := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      rw [e1, Equiv.sum_comp w (wtR ν), Equiv.sum_comp w (rhoV (N + 1))]
      linarith [hD.2])
    (by
      rw [hsq, hsq]
      exact hn)
  refine harm_of_perm lam hl ν hν w.symm (fun b => ?_)
  have h1 := hmain (w.symm b) (w.symm b).2
  rw [ex_val, ex_val] at h1
  simp only [hy, Equiv.apply_symm_apply, wtR, rhoV, m0] at h1
  have h2 : ((ν b : ℤ) : ℝ) = ((2 * lam (w.symm b) + (((N + 1 : ℕ) : ℤ) - 1) - (((w.symm b : Fin (N + 1)) : ℕ) : ℤ) -
      ((b : ℕ) : ℤ) : ℤ) : ℝ) := by
    push_cast at h1 ⊢
    linarith
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.RealCountG
