import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.KoszulBd

open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)

variable {n : ℕ} {ε : Fin n → Bool}

theorem sum_pick {R : Type} [AddCommGroup R] [Module ℂ R] (f : Fin n → Fin n → R) (a b : Fin n) (P : Prop)
    [Decidable P] (hP : P → ε a = true ∧ ε b = false) (Q : NC ε → Prop) [DecidablePred Q]
    (hQ : ∀ k, Q k ↔ P ∧ k.1.1 = a ∧ k.1.2 = b) :
    ∑ k : NC ε, (if Q k then (1 : ℂ) else 0) • f k.1.1 k.1.2 = if P then f a b else 0 := by
  by_cases hp : P
  · rw [if_pos hp]
    let k0 : NC ε := ⟨(a, b), hP hp⟩
    rw [Finset.sum_eq_single k0]
    · rw [if_pos ((hQ k0).mpr ⟨hp, rfl, rfl⟩), one_smul]
    · intro k _ hk
      rw [if_neg, zero_smul]
      intro hq
      obtain ⟨_, h1, h2⟩ := (hQ k).mp hq
      exact hk (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (fun hq => hp ((hQ k).mp hq).1), zero_smul]

section Abstract

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Ring R] [Algebra ℂ R]

omit [DecidableEq ι] in
theorem sq_zero (L A : ι → R) (hLL : ∀ i j, Commute (L i) (L j)) (hLA : ∀ i j, Commute (L i) (A j))
    (hAA : ∀ i j, A i * A j + A j * A i = 0) : (∑ i, L i * A i) * (∑ i, L i * A i) = 0 := by
  have key : (∑ i, L i * A i) * (∑ i, L i * A i) = ∑ i, ∑ j, L i * L j * (A i * A j) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, mul_assoc, ← mul_assoc (A i) (L j) (A j), ← (hLA j i).eq, mul_assoc]
  have hS : ∑ i, ∑ j, L i * L j * (A i * A j) + ∑ i, ∑ j, L i * L j * (A j * A i) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_add, hAA i j, mul_zero]
  have hS' : ∑ i, ∑ j, L i * L j * (A j * A i) = ∑ i, ∑ j, L i * L j * (A i * A j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(hLL j i).eq]
  rw [key]
  rw [hS'] at hS
  have h2 : (2 : ℂ) • ∑ i, ∑ j, L i * L j * (A i * A j) = 0 := by
    rw [two_smul]
    exact hS
  have h3 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
  simpa [smul_smul] using h3

omit [DecidableEq ι] [Algebra ℂ R] in

theorem commute_of_unitary_conjugate (T G : R) (L A : ι → R) (hTA : ∀ k, Commute T (A k)) (hGL : ∀ k, Commute G (L k))
    (h : ∑ k, (T * L k - L k * T) * A k + ∑ k, L k * (G * A k - A k * G) = 0) :
    Commute (T + G) (∑ k, L k * A k) := by
  have e : (T + G) * (∑ k, L k * A k) - (∑ k, L k * A k) * (T + G)
      = ∑ k, (T * L k - L k * T) * A k + ∑ k, L k * (G * A k - A k * G) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hG : G * (L k * A k) = L k * (G * A k) := by rw [← mul_assoc, (hGL k).eq, mul_assoc]
    have hT : L k * A k * T = L k * T * A k := by rw [mul_assoc, ← (hTA k).eq, ← mul_assoc]
    calc (T + G) * (L k * A k) - L k * A k * (T + G)
        = T * (L k * A k) + G * (L k * A k) - (L k * A k * T + L k * A k * G) := by
          rw [add_mul, mul_add]
      _ = T * (L k * A k) + L k * (G * A k) - (L k * T * A k + L k * A k * G) := by rw [hG, hT]
      _ = (T * L k - L k * T) * A k + L k * (G * A k - A k * G) := by noncomm_ring
  show (T + G) * _ = _ * (T + G)
  rw [← sub_eq_zero, e]
  exact h

theorem comm_ann (A C : ι → R) (q : ι → ι → ℂ) (hAA : ∀ i j, A i * A j + A j * A i = 0)
    (hAC : ∀ i j, A i * C j + C j * A i = if i = j then 1 else 0) (k : ι) :
    (∑ i, ∑ j, q i j • (C i * A j)) * A k - A k * (∑ i, ∑ j, q i j • (C i * A j)) = -∑ j, q k j • A j := by
  have hterm : ∀ i j, (q i j • (C i * A j)) * A k - A k * (q i j • (C i * A j))
      = -(if k = i then q i j • A j else 0) := by
    intro i j
    have h1 : A j * A k = -(A k * A j) := eq_neg_of_add_eq_zero_left (hAA j k)
    have h2 : A k * C i = (if k = i then 1 else 0) - C i * A k := eq_sub_of_add_eq (hAC k i)
    have h3 : C i * A j * A k - A k * (C i * A j) = -(if k = i then A j else 0) := by
      rw [mul_assoc, h1, ← mul_assoc (A k), h2]
      split_ifs <;> noncomm_ring
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, h3]
    split_ifs <;> simp
  have hrow : ∀ i, (∑ j, q i j • (C i * A j)) * A k - A k * (∑ j, q i j • (C i * A j))
      = ∑ j, -(if k = i then q i j • A j else 0) := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ => hrow i]
  rw [Finset.sum_eq_single k]
  · simp [Finset.sum_neg_distrib]
  · intro i _ hik
    simp [Ne.symm hik]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem comm_cre (A C : ι → R) (q : ι → ι → ℂ) (hCC : ∀ i j, C i * C j + C j * C i = 0)
    (hAC : ∀ i j, A i * C j + C j * A i = if i = j then 1 else 0) (k : ι) :
    (∑ i, ∑ j, q i j • (C i * A j)) * C k - C k * (∑ i, ∑ j, q i j • (C i * A j)) = ∑ i, q i k • C i := by
  have hterm : ∀ i j, (q i j • (C i * A j)) * C k - C k * (q i j • (C i * A j))
      = if j = k then q i j • C i else 0 := by
    intro i j
    have h1 : C k * C i = -(C i * C k) := eq_neg_of_add_eq_zero_left (hCC k i)
    have h2 : A j * C k = (if j = k then 1 else 0) - C k * A j := eq_sub_of_add_eq (hAC j k)
    have h3 : C i * A j * C k - C k * (C i * A j) = if j = k then C i else 0 := by
      rw [mul_assoc, h2, ← mul_assoc (C k), h1]
      split_ifs <;> noncomm_ring
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, h3]
    split_ifs <;> simp
  have hrow : ∀ i, (∑ j, q i j • (C i * A j)) * C k - C k * (∑ j, q i j • (C i * A j)) = q i k • C i := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => hterm i j]
    simp
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => hrow i

end Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_ann (T : Module.End ℂ V) (i : NC ε) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (ann i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  show T (ann i x A) = ann i (lift ε T x) A
  simp only [ann, LinearMap.coe_mk, AddHom.coe_mk, lift_apply]
  split_ifs
  · exact map_zero T
  · exact map_smul T _ _

theorem lift_cre (T : Module.End ℂ V) (i : NC ε) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  show T (cre i x A) = cre i (lift ε T x) A
  simp only [cre, LinearMap.coe_mk, AddHom.coe_mk, lift_apply]
  split_ifs
  · exact map_smul T _ _
  · exact map_zero T

theorem lift_Gop (T : Module.End ℂ V) (c d : Fin n) :
    Commute (Gop ε c d) (lift ε T : Module.End ℂ (Ch ε V)) := by
  unfold Gop
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => ?_
  exact ((lift_cre T i).symm.mul_left (lift_ann T j).symm).smul_left _

theorem glRel_lift (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    GlRel (fun a b => (lift ε (E a b) : Module.End ℂ (Ch ε V))) := by
  have hm : ∀ S U : Module.End ℂ V, (lift ε S : Module.End ℂ (Ch ε V)) * lift ε U = lift ε (S * U) :=
    fun S U => LinearMap.ext fun x => funext fun A => rfl
  have hs : ∀ S U : Module.End ℂ V, (lift ε S : Module.End ℂ (Ch ε V)) - lift ε U = lift ε (S - U) :=
    fun S U => LinearMap.ext fun x => funext fun A => rfl
  have h0 : (lift ε (0 : Module.End ℂ V) : Module.End ℂ (Ch ε V)) = 0 :=
    LinearMap.ext fun x => funext fun A => rfl
  intro a b c d
  try dsimp only
  rw [hm, hm, hs, hE a b c d]
  split_ifs <;> simp only [← h0, hs]

theorem bdFacts : CAR → BdFacts := by
  intro hCAR n ε V _ _ E hE
  have hAA : ∀ i j : NC ε, ann i * ann j + ann j * ann i = (0 : Module.End ℂ (Ch ε V)) :=
    fun i j => (hCAR n ε V i j).1
  have hCC : ∀ i j : NC ε, cre i * cre j + cre j * cre i = (0 : Module.End ℂ (Ch ε V)) :=
    fun i j => (hCAR n ε V i j).2.1
  have hAC : ∀ i j : NC ε, ann i * cre j + cre j * ann i = (if i = j then 1 else 0 : Module.End ℂ (Ch ε V)) :=
    fun i j => (hCAR n ε V i j).2.2
  have hGl := glRel_lift (ε := ε) E hE
  have hLL : ∀ i j : NC ε,
      Commute (lift ε (E i.1.1 i.1.2) : Module.End ℂ (Ch ε V)) (lift ε (E j.1.1 j.1.2)) := by
    intro i j
    have h1 : i.1.2 ≠ j.1.1 := by
      intro h'
      have a := i.2.2
      rw [h', j.2.1] at a
      exact absurd a (by decide)
    have h2 : j.1.2 ≠ i.1.1 := by
      intro h'
      have a := j.2.2
      rw [h', i.2.1] at a
      exact absurd a (by decide)
    have h := hGl i.1.1 i.1.2 j.1.1 j.1.2
    rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
    exact h
  refine ⟨sq_zero (fun i : NC ε => (lift ε (E i.1.1 i.1.2) : Module.End ℂ (Ch ε V))) ann hLL
    (fun i j => lift_ann _ j) hAA, ?_⟩
  intro c d hcd
  let qG : NC ε → NC ε → ℂ := fun i j =>
    (if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
      (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0)
  have hGop : Gop ε c d = ∑ i, ∑ j, qG i j • (cre i * ann j : Module.End ℂ (Ch ε V)) := rfl
  have hdiff : ∀ X Y : Module.End ℂ (Ch ε V), X - Y + (Y - X) = 0 := fun X Y => by abel
  constructor
  · show Commute (lift ε (E c d) + Gop ε c d) (∑ i, lift ε (E i.1.1 i.1.2) * ann i)
    refine commute_of_unitary_conjugate (lift ε (E c d)) (Gop ε c d)
      (fun k : NC ε => (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V))) ann
      (fun k => lift_ann _ k) (fun k => lift_Gop _ c d) ?_
    beta_reduce
    have hrow : ∀ k : NC ε, (lift ε (E c d) : Module.End ℂ (Ch ε V)) * lift ε (E k.1.1 k.1.2)
        - lift ε (E k.1.1 k.1.2) * lift ε (E c d)
        = (if d = k.1.1 then lift ε (E c k.1.2) else 0) - (if k.1.2 = c then lift ε (E k.1.1 d) else 0) :=
      fun k => hGl c d k.1.1 k.1.2
    have hcomm : ∀ k : NC ε, (Gop ε c d : Module.End ℂ (Ch ε V)) * ann k - ann k * Gop ε c d = -∑ j, qG k j • ann j := by
      intro k
      rw [hGop]
      exact comm_ann ann cre qG hAA hAC k
    have hsecond : ∑ k : NC ε, (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V)) * -∑ j : NC ε, qG k j • ann j
        = -∑ j : NC ε, (∑ k : NC ε, qG k j • (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V))) * ann j := by
      simp_rw [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      rw [Finset.sum_comm]
    have hpick : ∀ j : NC ε, ∑ k : NC ε, qG k j • (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V))
        = (if d = j.1.1 then lift ε (E c j.1.2) else 0) - (if j.1.2 = c then lift ε (E j.1.1 d) else 0) := by
      intro j
      simp only [qG, sub_smul, Finset.sum_sub_distrib]
      congr 1
      · exact sum_pick (fun x y => (lift ε (E x y) : Module.End ℂ (Ch ε V))) c j.1.2 (d = j.1.1)
          (fun h => ⟨hcd.trans (h ▸ j.2.1), j.2.2⟩) _
          (fun k => ⟨fun h => ⟨h.2.1.symm, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1.symm, h.2.2⟩⟩)
      · exact sum_pick (fun x y => (lift ε (E x y) : Module.End ℂ (Ch ε V))) j.1.1 d (j.1.2 = c)
          (fun h => ⟨j.2.1, hcd.symm.trans (h ▸ j.2.2)⟩) _
          (fun k => ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩)
    simp_rw [hrow, hcomm]
    rw [hsecond]
    simp_rw [hpick]
    exact add_neg_cancel _
  · show Commute (lift ε (E c d) + Gop ε c d) (∑ i, lift ε (E i.1.2 i.1.1) * cre i)
    refine commute_of_unitary_conjugate (lift ε (E c d)) (Gop ε c d)
      (fun k : NC ε => (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V))) cre
      (fun k => lift_cre _ k) (fun k => lift_Gop _ c d) ?_
    beta_reduce
    have hrow : ∀ k : NC ε, (lift ε (E c d) : Module.End ℂ (Ch ε V)) * lift ε (E k.1.2 k.1.1)
        - lift ε (E k.1.2 k.1.1) * lift ε (E c d)
        = (if d = k.1.2 then lift ε (E c k.1.1) else 0) - (if k.1.1 = c then lift ε (E k.1.2 d) else 0) :=
      fun k => hGl c d k.1.2 k.1.1
    have hcomm : ∀ k : NC ε, (Gop ε c d : Module.End ℂ (Ch ε V)) * cre k - cre k * Gop ε c d = ∑ i, qG i k • cre i := by
      intro k
      rw [hGop]
      exact comm_cre ann cre qG hCC hAC k
    have hsecond : ∑ k : NC ε, (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V)) * ∑ i : NC ε, qG i k • cre i
        = ∑ i : NC ε, (∑ k : NC ε, qG i k • (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V))) * cre i := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      rw [Finset.sum_comm]
    have hpick : ∀ i : NC ε, ∑ k : NC ε, qG i k • (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V))
        = (if i.1.1 = c then lift ε (E i.1.2 d) else 0) - (if d = i.1.2 then lift ε (E c i.1.1) else 0) := by
      intro i
      simp only [qG, sub_smul, Finset.sum_sub_distrib]
      congr 1
      · exact sum_pick (fun x y => (lift ε (E y x) : Module.End ℂ (Ch ε V))) d i.1.2 (i.1.1 = c)
          (fun h => ⟨hcd.symm.trans (h ▸ i.2.1), i.2.2⟩) _
          (fun k => ⟨fun h => ⟨h.1, h.2.1, h.2.2.symm⟩, fun h => ⟨h.1, h.2.1, h.2.2.symm⟩⟩)
      · exact sum_pick (fun x y => (lift ε (E y x) : Module.End ℂ (Ch ε V))) i.1.1 c (d = i.1.2)
          (fun h => ⟨i.2.1, hcd.trans (h ▸ i.2.2)⟩) _
          (fun k => ⟨fun h => ⟨h.1.symm, h.2.2.symm, h.2.1⟩, fun h => ⟨h.1.symm, h.2.2, h.2.1.symm⟩⟩)
    simp_rw [hrow, hcomm]
    rw [hsecond]
    simp_rw [hpick]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← add_mul, hdiff, zero_mul]

end GlobalTheory.CompanionTheory.KoszulBd
