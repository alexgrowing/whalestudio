import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset

noncomputable section

namespace CompanionTheory.D.LK

open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)

variable {n : ℕ} {ε : Fin n → Bool}

def tc (ε : Fin n → Bool) (i j k : Pos n) : ℂ := if Tri ε i j k then 1 else 0

def cc (ε : Fin n → Bool) (i : Pos n) : ℂ := if cpt ε i then 1 else 0

theorem tri_uniq {i j k k' : Pos n} (h : Tri ε i j k) (h' : Tri ε i j k') : k = k' :=
  Subtype.ext (Prod.ext (h.2.2.2.1.trans h'.2.2.2.1.symm) (h.2.2.2.2.trans h'.2.2.2.2.symm))

theorem sum_tc {M : Type} [AddCommGroup M] [Module ℂ M] (i j : Pos n) (f : Pos n → M) :
    ∑ k, tc ε i j k • f k = if h : cpt ε i ∧ cpt ε j ∧ i.1.2 = j.1.1 then
      f ⟨(i.1.1, j.1.2), i.2.trans (h.2.2 ▸ j.2)⟩ else 0 := by
  split_ifs with h
  · have ht : Tri ε i j ⟨(i.1.1, j.1.2), i.2.trans (h.2.2 ▸ j.2)⟩ := ⟨h.1, h.2.1, h.2.2, rfl, rfl⟩
    rw [Finset.sum_eq_single _ (fun k _ hk => by rw [tc, if_neg fun h' => hk (tri_uniq h' ht), zero_smul]) (by simp),
      tc, if_pos ht, one_smul]
  · exact Finset.sum_eq_zero fun k _ => by rw [tc, if_neg fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩, zero_smul]

theorem tc_assoc (p q r k : Pos n) : ∑ i, tc ε p q i * tc ε i r k = ∑ j, tc ε q r j * tc ε p j k := by
  have h1 := sum_tc (ε := ε) p q (fun i => tc ε i r k)
  have h2 := sum_tc (ε := ε) q r (fun j => tc ε p j k)
  simp only [smul_eq_mul] at h1 h2
  rw [h1, h2]
  obtain ⟨⟨a, b⟩, _⟩ := p
  obtain ⟨⟨b', c⟩, _⟩ := q
  obtain ⟨⟨c', d⟩, _⟩ := r
  simp only [tc, Tri, cpt]
  by_cases hb : b = b'
  · subst hb
    by_cases hc : c = c'
    · subst hc
      simp only [dite_eq_ite]
      cases ε a <;> cases ε b <;> cases ε c <;> cases ε d <;> simp
    · simp [hc]
  · simp [hb]

section Ring

variable {R : Type} [Ring R] [Algebra ℂ R] (E : Fin n → Fin n → R) (an cr : Pos n → R)

theorem self_neg {x : R} (h : x = -x) : x = 0 := by
  have : (2 : ℂ) • x = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h
  rw [← one_smul ℂ x, ← inv_mul_cancel₀ (two_ne_zero' ℂ), mul_smul, this, smul_zero]

theorem koszul_differential_sq (hE : KRel ε E) (h1 : ∀ a b i, Commute (E a b) (an i)) (haa : ∀ i j, an i * an j + an j * an i = 0) :
    (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) =
      ∑ i, ∑ j, ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) := by
  set T : Pos n → Pos n → R := fun i j => ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) with hT
  set U : Pos n → Pos n → R := fun i j => (cc ε i * cc ε j) • (E i.1.1 i.1.2 * E j.1.1 j.1.2 * (an i * an j)) with hU
  have e : (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) = ∑ i, ∑ j, U i j := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hU, mul_assoc, ← mul_assoc (an i), ← (h1 _ _ i).eq]
    simp only [mul_assoc]
  have key : ∀ i j, U i j + U j i = T i j + T j i := by
    intro i j
    have ha : an j * an i = -(an i * an j) := eq_neg_of_add_eq_zero_right (haa i j)
    simp only [hT, hU, sum_tc (f := fun k => E k.1.1 k.1.2 * (an i * an j)),
      sum_tc (f := fun k => E k.1.1 k.1.2 * (an j * an i))]
    rw [ha]
    by_cases ci : cpt ε i
    swap
    · simp [cc, ci]
    by_cases cj : cpt ε j
    swap
    · simp [cc, cj]
    have := hE i.1.1 i.1.2 j.1.1 j.1.2 ci cj
    simp only [cc, eq_true ci, eq_true cj, if_true, true_and, mul_one, one_smul, mul_neg, ← sub_eq_add_neg, ← sub_mul, this]
    split_ifs <;> simp [sub_mul, sub_eq_add_neg, add_mul]
  rw [e, ← sub_eq_zero]
  apply self_neg
  rw [eq_neg_iff_add_eq_zero]
  have s1 : ∑ i, ∑ j, U i j = ∑ i, ∑ j, U j i := Finset.sum_comm
  have s2 : ∑ i, ∑ j, T i j = ∑ i, ∑ j, T j i := Finset.sum_comm
  have s3 : ∑ i, ∑ j, U i j + ∑ i, ∑ j, U j i = ∑ i, ∑ j, T i j + ∑ i, ∑ j, T j i := by
    simp only [← Finset.sum_add_distrib, key]
  rw [← s1, ← s2] at s3
  change (∑ i, ∑ j, U i j - ∑ i, ∑ j, T i j) + (∑ i, ∑ j, U i j - ∑ i, ∑ j, T i j) = 0
  rw [sub_add_sub_comm, s3, sub_self]

theorem comm_aa (haa : ∀ i j, an i * an j + an j * an i = 0) (l i j : Pos n) : an j * an i * an l = an l * (an j * an i) := by
  have h : ∀ i j, an i * an j = -(an j * an i) := fun i j => eq_neg_of_add_eq_zero_left (haa i j)
  rw [mul_assoc, h i l, mul_neg, ← mul_assoc, h j l, neg_mul, neg_neg, mul_assoc]

theorem koszul_differential_anticommutator (h1 : ∀ a b i, Commute (E a b) (an i)) (h2 : ∀ a b i, Commute (E a b) (cr i))
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) +
      (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) =
      -∑ i, ∑ j, ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) := by
  simp only [Finset.mul_sum (s := univ) (f := fun i => ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)),
    Finset.sum_mul (s := univ) (f := fun i => ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)),
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have e : ∀ l : Pos n, cc ε l • (E l.1.1 l.1.2 * an l) * (cr k * an j * an i) +
      cr k * an j * an i * cc ε l • (E l.1.1 l.1.2 * an l) =
      if l = k then cc ε l • (E l.1.1 l.1.2 * (an j * an i)) else 0 := by
    intro l
    have c1 : cr k * an j * an i * (E l.1.1 l.1.2 * an l) = E l.1.1 l.1.2 * (cr k * an l * (an j * an i)) := by
      rw [← mul_assoc, ← (((h2 _ _ k).mul_right (h1 _ _ j)).mul_right (h1 _ _ i)).eq, mul_assoc, mul_assoc (cr k),
        mul_assoc (cr k), comm_aa an haa, mul_assoc (cr k)]
    have c2 : E l.1.1 l.1.2 * an l * (cr k * an j * an i) = E l.1.1 l.1.2 * (an l * cr k * (an j * an i)) := by
      simp only [mul_assoc]
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, c1, c2, ← mul_add, ← add_mul, hac]
    split_ifs <;> simp
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]
  rw [eq_neg_of_add_eq_zero_left (haa j i), tc]
  split_ifs with h
  · simp [cc, h.cptk]
  · simp

theorem beta_sq (haa : ∀ i j, an i * an j + an j * an i = 0) (hcc : ∀ i j, cr i * cr j + cr j * cr i = 0)
    (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) = 0 := by
  let t : Pos n × Pos n × Pos n → ℂ := fun p => tc ε p.1 p.2.1 p.2.2
  have e : (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) =
      ∑ p : Pos n × Pos n × Pos n, t p • (cr p.2.2 * an p.2.1 * an p.1) := by
    simp only [Fintype.sum_prod_type, t]
  have ex : ∀ i j k i' j' k' : Pos n, cr k * an j * an i * (cr k' * an j' * an i') =
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
  have h3 : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (cr p.2.2 * cr q.2.2 * ((an p.2.1 * an p.1) * (an q.2.1 * an q.1))) = 0 := by
    apply self_neg
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm (t q), eq_neg_of_add_eq_zero_left (hcc q.2.2 p.2.2), neg_mul, smul_neg, ← mul_assoc (an q.2.1 * an q.1),
      comm_aa an haa, mul_assoc (an p.2.1), comm_aa an haa, ← mul_assoc (an p.2.1)]
  rw [h3, add_zero, sub_eq_zero]
  have L : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (if p.1 = q.2.2 then cr p.2.2 * (an p.2.1 * (an q.2.1 * an q.1)) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ i, tc ε p q i * tc ε i r k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    symm
    calc _ = ∑ p, ∑ q, ∑ i, ∑ r, ∑ k, (tc ε p q i * tc ε i r k) • (cr k * (an r * an q * an p)) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          exact (Finset.sum_congr rfl fun r _ => Finset.sum_comm).trans Finset.sum_comm
      _ = ∑ x : Pos n × Pos n, ∑ y : Pos n × Pos n × Pos n,
            (tc ε x.1 x.2 y.1 * tc ε y.1 y.2.1 y.2.2) • (cr y.2.2 * (an y.2.1 * an x.2 * an x.1)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type, mul_comm (tc ε _ _ _) (tc ε _ _ _), mul_assoc]
  have R' : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (if p.2.1 = q.2.2 then cr p.2.2 * (an q.2.1 * an q.1 * an p.1) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ j, tc ε q r j * tc ε p j k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    calc _ = ∑ x : Pos n × Pos n, ∑ y : Pos n × Pos n,
            (tc ε p x.1 x.2 * tc ε y.1 y.2 x.1) • (cr x.2 * (an y.2 * an y.1 * an p)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
          simp only [mul_comm (tc ε p _ _)]
  rw [L, R']
  simp only [tc_assoc]

end Ring

theorem koszul_differential_sq_zero : BdSq := by
  intro n ε V _ _ E hE
  have e : bd ε E = (∑ i, cc ε i • ((lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i)) +
      ∑ i, ∑ j, ∑ k, tc ε i j k • (cre k * ann j * ann i : Module.End ℂ (Cn n V)) := by
    simp only [bd, cc, tc, ite_smul, one_smul, zero_smul]
  have hL : KRel ε fun a b => (lift n (E a b) : Module.End ℂ (Cn n V)) := by
    intro a b c d h1 h2
    refine LinearMap.ext fun x => funext fun A => ?_
    have := LinearMap.congr_fun (hE a b c d h1 h2) (x A)
    split_ifs at this ⊢ <;> simpa using this
  have h1 : ∀ a b i, Commute (lift n (E a b) : Module.End ℂ (Cn n V)) (ann i) :=
    fun a b i => LinearMap.ext fun y => lift_ann _ _ y
  have h2 : ∀ a b i, Commute (lift n (E a b) : Module.End ℂ (Cn n V)) (cre i) :=
    fun a b i => LinearMap.ext fun y => lift_cre _ _ y
  rw [e, add_mul, mul_add, mul_add, koszul_differential_sq _ ann hL h1 ann_ann, beta_sq ann cre ann_ann cre_cre ann_cre, add_zero,
    add_assoc, koszul_differential_anticommutator _ ann cre h1 h2 ann_ann ann_cre, add_neg_cancel]

end CompanionTheory.D.LK
