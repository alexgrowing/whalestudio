import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def beA (n0 : ℕ) (B : Fin N → ℕ) : ℕ := ∑ i : Fin N, if i.val < n0 then B i else 0

structure IsPATHa (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (dd : Fin N → ℕ) : Prop where
  path : ∃ P : PPath (r + K) N LL dd, P.mu = μ
  degs : ∀ i : Fin N, i.val < n0 → dd i = B i
  head : ∀ (i : Fin N) (m : Fin (r + K)), n0 ≤ i.val → m.val ≤ i.val - n0 → μ i.succ m = (beA n0 B : ℤ)

def posS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (la m) 0

def negS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (-la m) 0

def Xi (r K : ℕ) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ) (i : Fin N) : ℝ := La * bb i / ((p : ℝ) * ((r + K : ℕ) : ℝ))

def Typ [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N,
    (LL.vec i = false → ((posS (μ i.castSucc) - posS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (LL.vec i = true → r ≤ i.val → ((negS (μ i.castSucc) - negS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (r ≤ i.val → (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ))

def GoodA [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N, r ≤ i.val →
    (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (LL.vec i = true → ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤
      Xi r K bb La p i + 2 * (B (od i) : ℝ)) ∧
    (LL.vec i = false → ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ Xi r K bb La p i)

def rkA (r K n0 : ℕ) (B : Fin N → ℕ) : ℕ :=
  ∏ i : Fin N, if i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

structure HypT (N n0 r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ) : Prop where
  hN : N = n0 + r
  r1 : 1 ≤ r
  a3 : 3 ≤ a
  p13 : 13 ≤ p
  H1 : ∀ i : Fin N, i.val < n0 → ((r + K : ℕ) : ℝ) ≤ (B i : ℝ) ∧ (B i : ℝ) ≤ 2 * a
  H2 : ∀ i i' : Fin N, i < i' → i'.val < n0 → LL.vec i = LL.vec i' → (p : ℝ) ^ 2 / 5 * (B i : ℝ) ≤ (B i' : ℝ)
  vec_true_of_early : ∀ i : Fin N, i.val < r → LL.vec i = true
  vec_true_of_late : ∀ i : Fin N, n0 ≤ i.val + r → LL.vec i = true
  two_r_le_n0 : 2 * r ≤ n0
  N_add_r_le_K : N + r ≤ K
  H4 : ((r + K : ℕ) : ℝ) / 2 ≤ (K : ℝ) - 2 * (N : ℝ)
  N_le_a : (N : ℝ) ≤ a
  od_lt : ∀ i : Fin N, r ≤ i.val → od i < i
  od_vec : ∀ i : Fin N, r ≤ i.val → LL.vec (od i) = true
  od_card : ∀ i : Fin N, r ≤ i.val →
    (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true).card = r
  bb_pos : ∀ i : Fin N, r ≤ i.val → 0 < bb i
  bb_le : ∀ i l : Fin N, r ≤ i.val → l < i → l.val < n0 → (B l : ℝ) ≤ 4 * bb i / (p : ℝ)
  La_pos : 0 < La

def ell0 (N : ℕ) (a : ℝ) : ℝ := Real.log (1 + 2 * a * (N : ℝ))

abbrev QT (N r K : ℕ) := (Fin (N + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))

def SP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (Fin (N + 1) → Fin (r + K) → ℤ) :=
  {μ | ∃ dd, IsPATHa LL n0 B μ dd}

def SAll (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ IsSt (tanPart q.1) q.2}

def SGood [NeZero r] (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ)
    (p : ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ GoodA LL B od bb La p q.1 ∧ IsSt (tanPart q.1) q.2}

def PathWeightEqRank : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SAll (r := r) (K := K) LL n0 B).Finite ∧ (SAll (r := r) (K := K) LL n0 B).ncard = rkA r K n0 B

def PathCountFinite : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SP (r := r) (K := K) LL n0 B).Finite ∧
      ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a)

def AtypicalPathSmallWeight : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ¬ Typ LL B od bb La p μ →
      (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) ≤
        Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ)

def TypicalPathOrdersSmall : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, Typ LL B od bb La p μ → GoodA LL B od bb La p μ

def LemT : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SGood (r := r) (K := K) LL n0 B od bb La p).Finite ∧
      (1 - Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32)) * (rkA r K n0 B : ℝ) ≤
        ((SGood (r := r) (K := K) LL n0 B od bb La p).ncard : ℝ)

theorem lemT_of (ha : PathWeightEqRank) (hb : PathCountFinite) (hc : AtypicalPathSmallWeight) (hd : TypicalPathOrdersSmall) : LemT := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  obtain ⟨hfin, hcard⟩ := ha N n0 r K LL B od bb a La p H
  obtain ⟨hPfin, hPcard⟩ := hb N n0 r K LL B od bb a La p H
  have hc' := hc N n0 r K LL B od bb a La p H
  have hd' := hd N n0 r K LL B od bb a La p H
  set SA := SAll (r := r) (K := K) LL n0 B with hSA
  set SG := SGood (r := r) (K := K) LL n0 B od bb La p with hSG
  have hGA : SG ⊆ SA := fun q hq => ⟨hq.1, hq.2.2⟩
  have hGfin : SG.Finite := hfin.subset hGA
  refine ⟨hGfin, ?_⟩
  let SB : Set (QT N r K) := {q | q ∈ SA ∧ ¬ Typ LL B od bb La p q.1}
  have hBfin : SB.Finite := hfin.subset fun q hq => hq.1
  have hcov : SA ⊆ SG ∪ SB := by
    intro q hq
    by_cases ht : Typ LL B od bb La p q.1
    · exact Or.inl ⟨hq.1, hd' q.1 hq.1 ht, hq.2⟩
    · exact Or.inr ⟨hq, ht⟩
  have h1 : SA.ncard ≤ SG.ncard + SB.ncard :=
    le_trans (Set.ncard_le_ncard hcov (hGfin.union hBfin)) (Set.ncard_union_le _ _)
  set cR : ℝ := Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ) with hcR
  have hcR0 : 0 ≤ cR := by positivity

  have h2 : (SB.ncard : ℝ) ≤ ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) * cR := by
    rw [Set.ncard_eq_toFinset_card _ hBfin, Set.ncard_eq_toFinset_card _ hPfin]
    have hmaps : ∀ q ∈ hBfin.toFinset, q.1 ∈ hPfin.toFinset := by
      intro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      exact hq.1.1
    have hfib : ∀ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) ≤ cR := by
      intro μ hμ
      rw [Set.Finite.mem_toFinset] at hμ
      by_cases ht : Typ LL B od bb La p μ
      · have : hBfin.toFinset.filter (fun q => q.1 = μ) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro q hq hqμ
          rw [Set.Finite.mem_toFinset] at hq
          exact hq.2 (hqμ ▸ ht)
        rw [this]; simpa using hcR0
      · refine le_trans ?_ (hc' μ hμ ht)
        have hIfin : ({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).Finite := by
          refine (hfin.image Prod.snd).subset ?_
          intro I hI
          exact ⟨(μ, I), ⟨hμ, hI⟩, rfl⟩
        rw [Set.ncard_eq_toFinset_card _ hIfin]
        have : (hBfin.toFinset.filter fun q => q.1 = μ).card ≤ hIfin.toFinset.card := by
          refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
          · intro q hq
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.Finite.mem_toFinset] at hq
            simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
            have := hq.1.1.2
            rwa [hq.2] at this
          · intro q hq q' hq' hqq
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
            exact Prod.ext (hq.2.trans hq'.2.symm) hqq
        exact_mod_cast this
    have hsum : (hBfin.toFinset.card : ℝ) =
        ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := hBfin.toFinset) (t := hPfin.toFinset)
        (fun q hq => hmaps q hq)
      rw [this]; push_cast; rfl
    rw [hsum]
    calc ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ)
        ≤ ∑ _μ ∈ hPfin.toFinset, cR := Finset.sum_le_sum hfib
      _ = (hPfin.toFinset.card : ℝ) * cR := by rw [Finset.sum_const, nsmul_eq_mul]

  have hk0 : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by have := H.r1; omega
    exact_mod_cast this
  have hmin : min La ((r + K : ℕ) : ℝ) / 32 ≤
      min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12) := by
    have hH4 := H.H4
    refine le_min ?_ ?_
    · have h3 : La / 32 ≤ La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have := mul_le_mul_of_nonneg_left hH4 H.La_pos.le
        nlinarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) h3
    · have h3 : ((r + K : ℕ) : ℝ) / 32 ≤ ((K : ℝ) - 2 * N) / 12 := by linarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) h3
  have hrk0 : (0 : ℝ) ≤ (rkA r K n0 B : ℝ) := Nat.cast_nonneg _
  have h3 : (SB.ncard : ℝ) ≤
      Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32) * (rkA r K n0 B : ℝ) := by
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_right hPcard hcR0) ?_)
    rw [hcR, ← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hrk0
    linarith
  have h1' : (rkA r K n0 B : ℝ) ≤ (SG.ncard : ℝ) + (SB.ncard : ℝ) := by
    rw [← hcard]; exact_mod_cast h1
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf.T
