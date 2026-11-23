import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KoszulDifferentialAnticommutator

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.BdSqProof

open GlobalTheory.CompanionTheory.RealMult
open CompanionTheory.D.LK (Pos key tc)
open Formalism.REAL (GlRel)

section Ring

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Ring R] [Algebra ℂ R]
  (c : ι → ι → ι → ℂ) (L an cr : ι → R)

theorem comm_aa (haa : ∀ i j, an i * an j + an j * an i = 0) (l i j : ι) :
    an j * an i * an l = an l * (an j * an i) := by
  have h : ∀ i j, an i * an j = -(an j * an i) := fun i j => eq_neg_of_add_eq_zero_left (haa i j)
  rw [mul_assoc, h i l, mul_neg, ← mul_assoc, h j l, neg_mul, neg_neg, mul_assoc]

theorem self_neg {x : R} (h : x = -x) : x = 0 := by
  have : (2 : ℂ) • x = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h
  rw [← one_smul ℂ x, ← inv_mul_cancel₀ (two_ne_zero' ℂ), mul_smul, this, smul_zero]

theorem a_sq (hL : ∀ i j, L i * L j - L j * L i = ∑ k, c i j k • L k) (h1 : ∀ i j, Commute (L i) (an j))
    (haa : ∀ i j, an i * an j + an j * an i = 0) :
    (∑ i, L i * an i) * (∑ i, L i * an i) =
      (1 / 2 : ℂ) • ∑ i, ∑ j, ∑ k, c i j k • (L k * (an i * an j)) := by
  have e : (∑ i, L i * an i) * (∑ i, L i * an i) = ∑ i, ∑ j, L i * L j * (an i * an j) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← mul_assoc (an i), ← (h1 j i).eq]
    simp only [mul_assoc]
  have t : ∀ i j, ∑ k, c i j k • (L k * (an i * an j)) =
      L i * L j * (an i * an j) + L j * L i * (an j * an i) := by
    intro i j
    have ha : an j * an i = -(an i * an j) := eq_neg_of_add_eq_zero_right (haa i j)
    simp only [← smul_mul_assoc, ← Finset.sum_mul, ← hL, ha, mul_neg, ← sub_eq_add_neg, sub_mul]
  have s : ∑ i, ∑ j, L j * L i * (an j * an i) = ∑ i, ∑ j, L i * L j * (an i * an j) := Finset.sum_comm
  simp only [t, Finset.sum_add_distrib]
  rw [s, e, ← two_smul ℂ, smul_smul]
  norm_num

theorem cross (h1 : ∀ i j, Commute (L i) (an j)) (h2 : ∀ i j, Commute (L i) (cr j))
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, L i * an i) * (∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) +
      (∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) * (∑ i, L i * an i) =
      -∑ i, ∑ j, ∑ k, c i j k • (L k * (an i * an j)) := by
  simp only [Finset.mul_sum (s := univ) (f := fun i => ∑ j, ∑ k, c i j k • (cr k * an j * an i)),
    Finset.sum_mul (s := univ) (f := fun i => ∑ j, ∑ k, c i j k • (cr k * an j * an i)),
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have e : ∀ l : ι, L l * an l * (cr k * an j * an i) + cr k * an j * an i * (L l * an l) =
      if l = k then L l * (an j * an i) else 0 := by
    intro l
    have c1 : cr k * an j * an i * (L l * an l) = L l * (cr k * an l * (an j * an i)) := by
      rw [← mul_assoc, ← (((h2 l k).mul_right (h1 l j)).mul_right (h1 l i)).eq, mul_assoc, mul_assoc (cr k),
        mul_assoc (cr k), comm_aa an haa, mul_assoc (cr k)]
    have c2 : L l * an l * (cr k * an j * an i) = L l * (an l * cr k * (an j * an i)) := by
      simp only [mul_assoc]
    rw [c1, c2, ← mul_add, ← add_mul, hac]
    split_ifs <;> simp
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]
  rw [eq_neg_of_add_eq_zero_left (haa j i)]
  simp

theorem cyc_sum {M : Type} [AddCommGroup M] (g : ι → ι → ι → M) :
    ∑ p, ∑ q, ∑ r, g q r p = ∑ p, ∑ q, ∑ r, g p q r := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_comm

theorem cyc_zero {M : Type} [AddCommGroup M] [Module ℂ M] (F : ι → ι → ι → ι → ℂ) (X : ι → ι → ι → ι → M)
    (hX : ∀ k p q r, X k q r p = X k p q r) (hJ : ∀ p q r k, F p q r k + F q r p k + F r p q k = 0) :
    ∑ p, ∑ q, ∑ r, ∑ k, F p q r k • X k p q r = 0 := by
  have h0 : ∀ p q r, ∑ k, F p q r k • X k p q r + ∑ k, F q r p k • X k q r p + ∑ k, F r p q k • X k r p q = 0 := by
    intro p q r
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hX k q r p, hX k p q r, ← add_smul, ← add_smul, hJ, zero_smul]
  obtain ⟨f, hf⟩ : ∃ f : ι → ι → ι → M, ∀ p q r, f p q r = ∑ k, F p q r k • X k p q r := ⟨_, fun _ _ _ => rfl⟩
  simp only [← hf] at h0 ⊢
  have e1 : ∑ p, ∑ q, ∑ r, f q r p = ∑ p, ∑ q, ∑ r, f p q r := cyc_sum f
  have e2 : ∑ p, ∑ q, ∑ r, f r p q = ∑ p, ∑ q, ∑ r, f p q r := (cyc_sum fun p q r => f r p q).symm
  have h3 : ∑ p, ∑ q, ∑ r, (f p q r + f q r p + f r p q) = 0 :=
    Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ => h0 p q r
  simp only [Finset.sum_add_distrib] at h3
  rw [e1, e2] at h3
  generalize ∑ p, ∑ q, ∑ r, f p q r = S at h3
  have h4 : (3 : ℂ) • S = 0 := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul, h3]
  rw [← one_smul ℂ S, ← inv_mul_cancel₀ (three_ne_zero' ℂ), mul_smul, h4, smul_zero]

theorem cyc_zero' {M : Type} [AddCommGroup M] [Module ℂ M] (F : ι → ι → ι → ι → ℂ) (X : ι → ι → ι → ι → M)
    (hX : ∀ k p q r, X k q r p = X k p q r) (hJ : ∀ p q r k, F p q r k + F q r p k + F r p q k = 0) :
    ∑ p, ∑ q, ∑ r, ∑ k, (-F q r p k) • X k p q r = 0 := by
  have h := cyc_sum fun p q r => ∑ k, F p q r k • X k p q r
  rw [cyc_zero F X hX hJ] at h
  simp only [neg_smul, Finset.sum_neg_distrib]
  have e : ∑ p, ∑ q, ∑ r, ∑ k, F q r p k • X k p q r = ∑ p, ∑ q, ∑ r, ∑ k, F q r p k • X k q r p :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun k _ => by rw [hX k p q r]
  rw [e, h, neg_zero]

theorem b_sq (hanti : ∀ i j k, c i j k = -c j i k)
    (hJ : ∀ p q r k, ∑ i, c p q i * c i r k + ∑ i, c q r i * c i p k + ∑ i, c r p i * c i q k = 0)
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hcc : ∀ i j, cr i * cr j + cr j * cr i = 0)
    (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) * (∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) = 0 := by
  let t : ι × ι × ι → ℂ := fun p => c p.1 p.2.1 p.2.2
  have e : (∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) =
      ∑ p : ι × ι × ι, t p • (cr p.2.2 * an p.2.1 * an p.1) := by
    simp only [Fintype.sum_prod_type, t]
  have ex : ∀ i j k i' j' k' : ι, cr k * an j * an i * (cr k' * an j' * an i') =
      (if i = k' then cr k * (an j * (an j' * an i')) else 0) - (if j = k' then cr k * (an j' * an i' * an i) else 0) +
        cr k * cr k' * ((an j * an i) * (an j' * an i')) := by
    intro i j k i' j' k'
    have a1 := eq_sub_of_add_eq (hac i k')
    have a2 := eq_sub_of_add_eq (hac j k')
    calc _ = cr k * (an j * (an i * cr k')) * (an j' * an i') := by simp only [mul_assoc]
      _ = cr k * (an j * (if i = k' then 1 else 0) - (an j * cr k') * an i) * (an j' * an i') := by
          rw [a1, mul_sub, mul_assoc (an j)]
      _ = _ := by
          rw [a2, comm_aa an haa i i' j']
          split_ifs <;> noncomm_ring
  rw [e, Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm, ex, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h3 : ∑ p : ι × ι × ι, ∑ q : ι × ι × ι,
      (t p * t q) • (cr p.2.2 * cr q.2.2 * ((an p.2.1 * an p.1) * (an q.2.1 * an q.1))) = 0 := by
    apply self_neg
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm (t q), eq_neg_of_add_eq_zero_left (hcc q.2.2 p.2.2), neg_mul, smul_neg, ← mul_assoc (an q.2.1 * an q.1),
      comm_aa an haa, mul_assoc (an p.2.1), comm_aa an haa, ← mul_assoc (an p.2.1)]
  rw [h3, add_zero, sub_eq_zero]
  have L' : ∑ p : ι × ι × ι, ∑ q : ι × ι × ι,
      (t p * t q) • (if p.1 = q.2.2 then cr p.2.2 * (an p.2.1 * (an q.2.1 * an q.1)) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ i, c p q i * c i r k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    symm
    calc _ = ∑ p, ∑ q, ∑ i, ∑ r, ∑ k, (c p q i * c i r k) • (cr k * (an r * an q * an p)) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          exact (Finset.sum_congr rfl fun r _ => Finset.sum_comm).trans Finset.sum_comm
      _ = ∑ x : ι × ι, ∑ y : ι × ι × ι,
            (c x.1 x.2 y.1 * c y.1 y.2.1 y.2.2) • (cr y.2.2 * (an y.2.1 * an x.2 * an x.1)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type, mul_comm (c _ _ _) (c _ _ _), mul_assoc]
  have R' : ∑ p : ι × ι × ι, ∑ q : ι × ι × ι,
      (t p * t q) • (if p.2.1 = q.2.2 then cr p.2.2 * (an q.2.1 * an q.1 * an p.1) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ j, c q r j * c p j k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    calc _ = ∑ x : ι × ι, ∑ y : ι × ι,
            (c p x.1 x.2 * c y.1 y.2 x.1) • (cr x.2 * (an y.2 * an y.1 * an p)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
          simp only [mul_comm (c p _ _)]
  rw [L', R']
  have hX : ∀ k p q r, cr k * (an p * an r * an q) = cr k * (an r * an q * an p) := by
    intro k p q r
    rw [comm_aa an haa p q r, mul_assoc]
  have z1 := cyc_zero (fun p q r k => ∑ i, c p q i * c i r k) (fun k p q r => cr k * (an r * an q * an p)) hX hJ
  have z2 := cyc_zero' (fun p q r k => ∑ i, c p q i * c i r k) (fun k p q r => cr k * (an r * an q * an p)) hX hJ
  have hG : ∀ p q r k, ∑ j, c q r j * c p j k = -∑ i, c q r i * c i p k := by
    intro p q r k
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hanti p j k]; ring
  simp only [hG]
  exact z1.trans z2.symm

theorem d_sq (hL : ∀ i j, L i * L j - L j * L i = ∑ k, c i j k • L k) (h1 : ∀ i j, Commute (L i) (an j))
    (h2 : ∀ i j, Commute (L i) (cr j)) (hanti : ∀ i j k, c i j k = -c j i k)
    (hJ : ∀ p q r k, ∑ i, c p q i * c i r k + ∑ i, c q r i * c i p k + ∑ i, c r p i * c i q k = 0)
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hcc : ∀ i j, cr i * cr j + cr j * cr i = 0)
    (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    ((∑ i, L i * an i) + (1 / 2 : ℂ) • ∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) *
      ((∑ i, L i * an i) + (1 / 2 : ℂ) • ∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) = 0 := by
  have hA := a_sq c L an hL h1 haa
  have hC := cross c L an cr h1 h2 haa hac
  have hB := b_sq c an cr hanti hJ haa hcc hac
  generalize (∑ i, L i * an i) = A at *
  generalize (∑ i, ∑ j, ∑ k, c i j k • (cr k * an j * an i)) = B at *
  generalize (∑ i, ∑ j, ∑ k, c i j k • (L k * (an i * an j))) = T at *
  rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, hB, smul_zero, smul_zero,
    add_zero, add_assoc, ← smul_add, hC, hA, smul_neg, add_neg_cancel]

end Ring

section Constants

variable {n : ℕ}

theorem cst_anti (i j k : Ix n) : cst i j k = -cst j i k := by
  simp only [cst, cp, Bool.and_comm j.1]
  split_ifs <;> simp

theorem cp_eq (p q r : Pos n) :
    cp p q r = tc (CompanionTheory.D.LK.allT n) p q r - tc (CompanionTheory.D.LK.allT n) q p r := by
  have h : ∀ a b : Pos n, CompanionTheory.D.LK.Tri (CompanionTheory.D.LK.allT n) a b r ↔ (a.1.2 = b.1.1 ∧ r.1 = (a.1.1, b.1.2)) := by
    intro a b
    simp [CompanionTheory.D.LK.Tri, Prod.ext_iff]
  simp only [cp, tc, h]

theorem cp_jacobi (p q r k : Pos n) :
    ∑ m, cp p q m * cp m r k + ∑ m, cp q r m * cp m p k + ∑ m, cp r p m * cp m q k = 0 := by
  have e : ∀ a b c : Pos n, ∑ m, cp a b m * cp m c k =
      ∑ m, tc (CompanionTheory.D.LK.allT n) a b m * tc (CompanionTheory.D.LK.allT n) m c k -
      ∑ m, tc (CompanionTheory.D.LK.allT n) c a m * tc (CompanionTheory.D.LK.allT n) m b k -
      ∑ m, tc (CompanionTheory.D.LK.allT n) b a m * tc (CompanionTheory.D.LK.allT n) m c k +
      ∑ m, tc (CompanionTheory.D.LK.allT n) c b m * tc (CompanionTheory.D.LK.allT n) m a k := by
    intro a b c
    rw [CompanionTheory.D.LK.tc_assoc c a b k, CompanionTheory.D.LK.tc_assoc c b a k]
    simp only [cp_eq, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e, e, e]
  ring

theorem sum_cst (p q r k : Ix n) : ∑ i, cst p q i * cst i r k =
    if k.1 = (p.1 && q.1 && r.1) then ∑ m, cp p.2 q.2 m * cp m r.2 k.2 else 0 := by
  obtain ⟨s, p⟩ := p
  obtain ⟨t, q⟩ := q
  obtain ⟨u, r⟩ := r
  obtain ⟨w, k⟩ := k
  rw [Fintype.sum_prod_type]
  cases s <;> cases t <;> cases u <;> cases w <;> simp [cst]

theorem cst_jacobi (p q r k : Ix n) :
    ∑ i, cst p q i * cst i r k + ∑ i, cst q r i * cst i p k + ∑ i, cst r p i * cst i q k = 0 := by
  rw [sum_cst, sum_cst, sum_cst]
  have h1 : (q.1 && r.1 && p.1) = (p.1 && q.1 && r.1) := by cases p.1 <;> cases q.1 <;> cases r.1 <;> rfl
  have h2 : (r.1 && p.1 && q.1) = (p.1 && q.1 && r.1) := by cases p.1 <;> cases q.1 <;> cases r.1 <;> rfl
  rw [h1, h2]
  split_ifs
  · exact cp_jacobi _ _ _ _
  · simp

end Constants

section Letters

variable {n : ℕ}

theorem key_lt (p : Pos n) : key p < n * n := by
  have ha := p.1.1.2
  have hb := p.1.2.2
  calc key p = (p.1.1 : ℕ) * n + (p.1.2 : ℕ) := rfl
    _ < (p.1.1 : ℕ) * n + n := by omega
    _ = ((p.1.1 : ℕ) + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right n ha

theorem keyR_inj {i j : Ix n} (h : keyR i = keyR j) : i = j := by
  obtain ⟨s, p⟩ := i
  obtain ⟨t, q⟩ := j
  have hp := key_lt p
  have hq := key_lt q
  have hk : key p = key q → p = q := fun e => CompanionTheory.D.LK.Car.key_inj e
  cases s <;> cases t <;> simp only [keyR, Bool.false_eq_true, if_false, if_true] at h
  · rw [hk (by omega)]
  · omega
  · omega
  · rw [hk (by omega)]

def tw (i j : Ix n) : ℂ := if keyR j < keyR i then -1 else 1

theorem tw_self (i : Ix n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Ix n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Ix n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyR i ≠ keyR j := fun e => h (keyR_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

theorem sg_mul_self (i : Ix n) (A : Finset (Ix n)) : sgR i A * sgR i A = 1 := by
  unfold sgR
  rw [← mul_pow]; simp

theorem sg_insert (i : Ix n) {j : Ix n} {A : Finset (Ix n)} (h : j ∉ A) :
    sgR i (insert j A) = tw i j * sgR i A := by
  unfold sgR tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sg_erase (i : Ix n) {j : Ix n} {A : Finset (Ix n)} (h : j ∈ A) :
    sgR i (A.erase j) = tw i j * sgR i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : Ix n) (x : Cr n V) (A : Finset (Ix n)) :
    annR i x A = if i ∈ A then 0 else sgR i A • x (insert i A) := rfl

theorem cre_apply (i : Ix n) (x : Cr n V) (A : Finset (Ix n)) :
    creR i x A = if i ∈ A then sgR i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : Ix n) : (annR i * annR j + annR j * annR i : Module.End ℂ (Cr n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    ann_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgR i A * (-tw i j * sgR j A) + sgR j A * (tw i j * sgR i A) = 0 := by ring
  rw [this, zero_smul]

theorem cre_cre (i j : Ix n) : (creR i * creR j + creR j * creR i : Module.End ℂ (Cr n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    cre_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgR i A * (-tw i j * sgR j A) + sgR j A * (tw i j * sgR i A) = 0 := by ring
  rw [this, zero_smul]

theorem ann_cre (i j : Ix n) :
    (annR i * creR j + creR j * annR i : Module.End ℂ (Cr n V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, ann_apply, cre_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]
    · simp [hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sgR i A * (-tw i j * sgR j A) + sgR j A * (tw i j * sgR i A) = 0 := by ring
  rw [this, zero_smul]

theorem lift_apply (T : V →ₗ[ℂ] V) (x : Cr n V) (A : Finset (Ix n)) : liftR n T x A = T (x A) := rfl

theorem lift_ann (T : Module.End ℂ V) (i : Ix n) :
    Commute (liftR n T : Module.End ℂ (Cr n V)) (annR i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, lift_apply, ann_apply]
  split_ifs <;> simp

theorem lift_cre (T : Module.End ℂ V) (i : Ix n) :
    Commute (liftR n T : Module.End ℂ (Cr n V)) (creR i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, lift_apply, cre_apply]
  split_ifs <;> simp

theorem sum_one {M : Type} [AddCommGroup M] [Module ℂ M] (G : Fin n → Fin n → M) (p q : Pos n) :
    ∑ r : Pos n, (if p.1.2 = q.1.1 ∧ r.1 = (p.1.1, q.1.2) then (1 : ℂ) else 0) • G r.1.1 r.1.2 =
      if p.1.2 = q.1.1 then G p.1.1 q.1.2 else 0 := by
  split_ifs with h
  · have hlt : p.1.1 < q.1.2 := p.2.trans (h ▸ q.2)
    rw [Finset.sum_eq_single (⟨(p.1.1, q.1.2), hlt⟩ : Pos n)]
    · simp [h]
    · intro r _ hr
      rw [if_neg fun e => hr (Subtype.ext e.2), zero_smul]
    · simp
  · exact Finset.sum_eq_zero fun r _ => by rw [if_neg fun e => h e.1, zero_smul]

theorem sum_cp {M : Type} [AddCommGroup M] [Module ℂ M] (G : Fin n → Fin n → M) (p q : Pos n) :
    ∑ r : Pos n, cp p q r • G r.1.1 r.1.2 =
      (if p.1.2 = q.1.1 then G p.1.1 q.1.2 else 0) - (if q.1.2 = p.1.1 then G q.1.1 p.1.2 else 0) := by
  simp only [cp, sub_smul, Finset.sum_sub_distrib, sum_one]

theorem glK {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : Pair2 E1 E2) :
    GlRel fun a b => E1 a b + E2 a b := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have h3 := h.comm a b c d
  have h4 := h.comm c d a b
  have e : (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [add_mul, mul_add, h3, ← h4]
    abel
  rw [e, h1, h2]
  split_ifs <;> simp <;> abel

theorem rl_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : Pair2 E1 E2) (i j : Ix n) :
    rl E1 E2 i * rl E1 E2 j - rl E1 E2 j * rl E1 E2 i = ∑ k, cst i j k • rl E1 E2 k := by
  obtain ⟨s, p⟩ := i
  obtain ⟨t, q⟩ := j
  have e : ∑ k, cst (s, p) (t, q) k • rl E1 E2 k =
      ∑ r : Pos n, cp p q r • rl E1 E2 (s && t, r) := by
    rw [Fintype.sum_prod_type]
    cases s <;> cases t <;> simp [cst]
  rw [e]
  have hK := glK h p.1.1 p.1.2 q.1.1 q.1.2
  have h2 := h.gl2 p.1.1 p.1.2 q.1.1 q.1.2
  have c1 := h.comm p.1.1 p.1.2 q.1.1 q.1.2
  have c2 := h.comm q.1.1 q.1.2 p.1.1 p.1.2
  cases s <;> cases t
  · simpa only [rl, Bool.and_self, Bool.false_eq_true, if_false, sum_cp (fun a b => E2 a b)] using h2
  · simp only [rl, Bool.false_and, Bool.false_eq_true, if_false, if_true, sum_cp (fun a b => E2 a b)]
    rw [← h2, mul_add, add_mul, c2]
    abel
  · simp only [rl, Bool.and_false, Bool.false_eq_true, if_false, if_true, sum_cp (fun a b => E2 a b)]
    rw [← h2, mul_add, add_mul, c1]
    abel
  · simpa only [rl, Bool.and_self, if_true, sum_cp (fun a b => E1 a b + E2 a b)] using hK

end Letters

theorem bdSqR : BdSqR := by
  intro n V _ _ E1 E2 h
  have hL : ∀ i j : Ix n, (liftR n (rl E1 E2 i) : Module.End ℂ (Cr n V)) * liftR n (rl E1 E2 j) -
      liftR n (rl E1 E2 j) * liftR n (rl E1 E2 i) = ∑ k, cst i j k • (liftR n (rl E1 E2 k) : Module.End ℂ (Cr n V)) := by
    intro i j
    refine LinearMap.ext fun x => funext fun A => ?_
    have := LinearMap.congr_fun (rl_comm h i j) (x A)
    simpa [lift_apply, LinearMap.sum_apply, Finset.sum_apply] using this
  exact d_sq cst (fun i => (liftR n (rl E1 E2 i) : Module.End ℂ (Cr n V))) annR creR hL
    (fun i j => lift_ann _ j) (fun i j => lift_cre _ j) cst_anti cst_jacobi ann_ann cre_cre ann_cre

end GlobalTheory.CompanionTheory.RealMult.BdSqProof
