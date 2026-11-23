import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARSqB

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem csq_dd_pt {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (i a j b : Fin n) :
    E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a) =
      (if i = j then E a b * (cp i a * cm j b) else 0) - (if b = a then E j i * (cp i a * cm j b) else 0) +
        (if b = a then (if j = i then E i a * E a i else 0) else 0) := by
  have c1 : E j b * cp i a = cp i a * E j b := (hEC j b i a).1
  have c2 : E a i * cm j b = cm j b * E a i := (hEC a i j b).2
  have hcar : cm j b * cp i a = (if j = i ∧ b = a then 1 else 0) - cp i a * cm j b :=
    eq_sub_of_add_eq (hC j b i a).2.2
  have hgl : E a i * E j b =
      E j b * E a i + ((if i = j then E a b else 0) - (if b = a then E j i else 0)) := by
    rw [← hE a i j b]; abel
  have step : E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a) =
      E a i * E j b * (cp i a * cm j b) + E j b * E a i * (cm j b * cp i a) := by
    calc _ = E a i * (E j b * cp i a) * cm j b + E j b * (E a i * cm j b) * cp i a := by
            rw [c1, c2]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [step, hgl, hcar]
  rcases eq_or_ne i j with h1 | h1 <;> rcases eq_or_ne b a with h2 | h2
  · subst h1; subst h2
    simp only [eq_self_iff_true, and_self, if_true]
    noncomm_ring
  · subst h1
    simp only [eq_self_iff_true, if_true, h2, if_false, and_false]
    noncomm_ring
  · subst h2
    simp only [eq_self_iff_true, if_true, h1, Ne.symm h1, if_false, false_and]
    noncomm_ring
  · simp only [h1, h2, Ne.symm h1, if_false, and_false, false_and]
    noncomm_ring

theorem dd_add {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) :
    dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp =
      -(∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i) + crossT ε E cp cm := by
  have e1 : dOp ε E cp * dOp' ε E cm =
      -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        E a i * cp i a * (E j b * cm j b) := by
    unfold dOp dOp'
    rw [mul_neg, Finset.sum_mul_sum, neg_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_mul_sum]
    exact Finset.sum_comm
  have e2 : dOp' ε E cm * dOp ε E cp =
      -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        E j b * cm j b * (E a i * cp i a) := by
    unfold dOp dOp'
    rw [neg_mul, Finset.sum_mul_sum, neg_inj]
    simp only [Finset.sum_mul_sum]
    calc ∑ j ∈ plusIdx ε, ∑ i ∈ plusIdx ε, ∑ b ∈ minusIdx ε, ∑ a ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a)
        = ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε, ∑ a ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a) := Finset.sum_comm
      _ = ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hX : dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp =
      -(∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a))) := by
    rw [e1, e2]
    simp only [Finset.sum_add_distrib]
    abel
  have hA : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if i = j then E a b * (cp i a * cm j b) else 0) =
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a b * (cp i a * cm i b) := by
    have h1 : ∀ i ∈ plusIdx ε, ∀ a, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (if i = j then E a b * (cp i a * cm j b) else 0) =
        ∑ b ∈ minusIdx ε, E a b * (cp i a * cm i b) := by
      intro i hi a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_ite_eq, if_pos hi]
    refine (Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a _ => h1 i hi a).trans ?_
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm)
  have hB : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if b = a then E j i * (cp i a * cm j b) else 0) =
      ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, ∑ c ∈ minusIdx ε, E x y * (cp y c * cm x c) := by
    have h1 : ∀ i, ∀ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (if b = a then E j i * (cp i a * cm j b) else 0) =
        ∑ j ∈ plusIdx ε, E j i * (cp i a * cm j a) := by
      intro i a ha
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq', if_pos ha]
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a ha => h1 i a ha).trans ?_
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  have hC' : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if b = a then (if j = i then E i a * E a i else 0) else 0) =
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_congr rfl fun j _ => (by rw [Finset.sum_ite_eq', if_pos ha] :
      ∑ b ∈ minusIdx ε, (if b = a then (if j = i then E i a * E a i else 0) else 0) =
        (if j = i then E i a * E a i else 0))]
    rw [Finset.sum_ite_eq', if_pos hi]
  have hcross : crossT ε E cp cm =
      ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, ∑ c ∈ minusIdx ε, E x y * (cp y c * cm x c) -
        ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a b * (cp i a * cm i b) := by
    unfold crossT
    rw [sub_eq_add_neg]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      rw [csq_sgE_pp ε cp cm hy hx, Finset.mul_sum]
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [csq_sgE_mm ε cp cm hb ha, mul_neg, Finset.mul_sum]
  rw [hX]
  simp only [csq_dd_pt hE hC hEC, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB, hC', hcross]
  abel

private theorem sum_sum_ne_eps_eq_plusIdx_minusIdx_add (ε : Fin n → Bool) {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ¬ ε b = ε a), f a b =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, f x y + ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, f a b := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true)]
  have hm : univ.filter (fun a => ¬ ε a = true) = minusIdx ε := by
    ext a; simp [minusIdx]
  rw [hm]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [minusIdx, ha']
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [plusIdx, ha']

theorem two_D_sq {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) =
      -casimir E + casimirK ε (diagE ε E cp cm) -
        (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε E cp cm a a := by
  have hsq : (dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm) =
      dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp := by
    rw [add_mul, mul_add, mul_add, dOp_sq hE hC hEC, dOp'_sq hE hC hEC]
    abel
  have hs : ∑ a, ∑ b ∈ univ.filter (fun b => ¬ ε b = ε a), E a b * E b a =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a :=
    sum_sum_ne_eps_eq_plusIdx_minusIdx_add ε (fun a b => E a b * E b a)
  have hoff : casimir E = casimirK ε E +
      (∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a) := by
    rw [← hs]
    unfold casimir casimirK
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : ∀ a i : Fin n, E a i * E i a = E i a * E a i + (E a a - E i i) := by
    intro a i
    have h := hE a i i a
    rw [if_pos rfl, if_pos rfl] at h
    rw [← h]
    abel
  have hcomm2 : ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a i * E i a =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        (((plusIdx ε).card : ℂ) • ∑ a ∈ minusIdx ε, E a a -
          ((minusIdx ε).card : ℂ) • ∑ i ∈ plusIdx ε, E i i) := by
    rw [show ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a i * E i a =
        ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, (E i a * E a i + (E a a - E i i)) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => h1 a i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    refine congrArg₂ (· + ·) Finset.sum_comm (congrArg₂ (· - ·) ?_ ?_)
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
    · rw [Finset.sum_comm, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hrho : (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • E a a =
      ((minusIdx ε).card : ℂ) • ∑ i ∈ plusIdx ε, E i i -
        ((plusIdx ε).card : ℂ) • ∑ a ∈ minusIdx ε, E a a := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true)]
    have hm : univ.filter (fun a => ¬ ε a = true) = minusIdx ε := by
      ext a; simp [minusIdx]
    rw [hm]
    have e1 : ∑ a ∈ univ.filter (fun a => ε a = true), ((rhoHol ε a : ℝ) : ℂ) • E a a =
        (((minusIdx ε).card : ℂ) / 2) • ∑ i ∈ plusIdx ε, E i i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : ε a = true := (Finset.mem_filter.mp ha).2
      rw [show rhoHol ε a = ((minusIdx ε).card : ℝ) / 2 by simp [rhoHol, ha', qOf, minusIdx]]
      push_cast
      rfl
    have e2 : ∑ a ∈ minusIdx ε, ((rhoHol ε a : ℝ) : ℂ) • E a a =
        (-((plusIdx ε).card : ℂ) / 2) • ∑ a ∈ minusIdx ε, E a a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : ε a = false := (Finset.mem_filter.mp ha).2
      rw [show rhoHol ε a = -((plusIdx ε).card : ℝ) / 2 by simp [rhoHol, ha', pOf, plusIdx]]
      push_cast
      rfl
    rw [e1, e2, smul_add, smul_smul, smul_smul, sub_eq_add_neg, ← neg_smul]
    exact congrArg₂ (· + ·) (congrArg (· • _) (by ring)) (congrArg (· • _) (by ring))
  rw [hsq, dd_add hE hC hEC, casimirK_diagE hEC, casimirK_sgE hC, hoff, hcomm2]
  simp only [diagE, smul_add, Finset.sum_add_distrib, smul_neg]
  rw [hrho, two_smul ℂ (∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x)]
  abel

end ReciprocityTheory.ChartRestriction.DS
