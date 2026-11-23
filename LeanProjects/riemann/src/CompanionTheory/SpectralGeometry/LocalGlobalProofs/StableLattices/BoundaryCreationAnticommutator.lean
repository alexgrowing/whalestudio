import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Cartan

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem anticommutator_triple_product {R : Type*} [Ring R] (K Aj Ai C d₁ d₂ : R) (h₁ : Ai * C + C * Ai = d₁)
    (h₂ : Aj * C + C * Aj = d₂) (h₃ : K * C + C * K = 0) :
    K * Aj * Ai * C + C * (K * Aj * Ai) = K * Aj * d₁ - K * d₂ * Ai := by
  subst h₁ h₂
  have h : C * K = -(K * C) := eq_neg_of_add_eq_zero_right h₃
  have h' : C * (K * Aj * Ai) = -(K * C * Aj * Ai) := by
    rw [← mul_assoc, ← mul_assoc, h]; noncomm_ring
  rw [h']
  noncomm_ring

theorem tri_anti (i j k e : Pos n) :
    (cre k * ann j * ann i * cre e + cre e * (cre k * ann j * ann i) : Module.End ℂ (Cn n V)) =
      (if i = e then cre k * ann j else 0) - (if j = e then cre k * ann i else 0) := by
  rw [anticommutator_triple_product _ _ _ _ _ _ (CompanionTheory.D.LK.Car.ann_cre i e) (CompanionTheory.D.LK.Car.ann_cre j e)
    (CompanionTheory.D.LK.Car.cre_cre k e)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem cre_mul_lift (φ : Module.End ℂ V) (e : Pos n) :
    (cre e * (lift n φ : Module.End ℂ (Cn n V)) : Module.End ℂ (Cn n V)) = (lift n φ : Module.End ℂ (Cn n V)) * cre e :=
  LinearMap.ext fun x => (CompanionTheory.D.LK.lift_cre φ e x).symm

theorem part_one (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    ((∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0 :
      Module.End ℂ (Cn n V)) = lift n (E e.1.1 e.1.2) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h : ∀ i : Pos n,
      ((if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) :
        Module.End ℂ (Cn n V)) = if i = e then (lift n (E e.1.1 e.1.2) : Module.End ℂ (Cn n V)) else 0 := by
    intro i
    rw [if_pos (rfl : cpt (allT n) i), ← mul_assoc (cre e), cre_mul_lift, mul_assoc, mul_assoc, ← mul_add,
      CompanionTheory.D.LK.Car.ann_cre]
    by_cases hi : i = e
    · subst hi; simp
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

theorem sum_anti {R : Type*} [Ring R] (T P Q : Pos n → Pos n → Pos n → R) (c : R)
    (h : ∀ i j k, T i j k * c + c * T i j k = P i j k - Q i j k) :
    (∑ i, ∑ j, ∑ k, T i j k) * c + c * ∑ i, ∑ j, ∑ k, T i j k =
      ∑ i, ∑ j, ∑ k, P i j k - ∑ i, ∑ j, ∑ k, Q i j k := by
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, h, Finset.sum_sub_distrib]

theorem part_two (e : Pos n) :
    ((∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0 : Module.End ℂ (Cn n V)) = adL e.1.1 e.1.2 := by
  have h : ∀ i j k : Pos n,
      ((if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) : Module.End ℂ (Cn n V)) =
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0) -
        (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0) := by
    intro i j k
    by_cases ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
    · rw [if_pos ⟨rfl, rfl, ht⟩, tri_anti]
      obtain ⟨t1, t2, t3⟩ := ht
      congr 1
      · by_cases hi : i = e
        · subst hi
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hi, if_neg fun c => hi c.1]
      · by_cases hj : j = e
        · subst hj
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hj, if_neg fun c => hj c.1]
    · rw [if_neg fun c => ht c.2.2, zero_mul, mul_zero, add_zero, if_neg, if_neg, sub_zero]
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
  rw [sum_anti _ _ _ _ h]
  have s₁ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V))) =
      ∑ j : Pos n, ∑ k : Pos n,
        (if e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V)) := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have s₂ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V))) =
      ∑ i : Pos n, ∑ k : Pos n,
        (if i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [s₁, s₂]
  simp only [adL, adC, sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib]

theorem cartan (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2 := by
  have h₁ := part_one E e
  have h₂ := part_two (V := V) e
  unfold bd lF
  rw [add_mul, mul_add, add_add_add_comm, h₁, h₂]

end GlobalTheory.CompanionTheory.Cartan
