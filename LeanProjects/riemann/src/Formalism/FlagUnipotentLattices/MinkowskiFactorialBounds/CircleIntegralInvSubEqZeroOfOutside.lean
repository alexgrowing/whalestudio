import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Formalism.FormalDegreeBessel.FinalDS

namespace Formalism.HermitianLatticeCounting.P

section G1
open Finset Polynomial

end G1

section G2
open Finset Metric

end G2

section G3
open Finset Polynomial Formalism.HermitianLatticeCounting.ExpansionTerms

end G3

section G4
open Finset Formalism.HermitianLatticeCounting.ExpansionTerms

end G4

section G5
open Finset

theorem degree_ratio_minus_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.DegRatioMinus := by
  intro n μ s hμ hint hinj
  have hadd : (μ - Pi.single s 1) + Pi.single s 1 = μ := sub_add_cancel _ _
  have hint' : ∀ a b, ∃ m : ℤ, (μ - Pi.single s 1 : Fin n → ℝ) a - (μ - Pi.single s 1 : Fin n → ℝ) b = (m : ℝ) := by
    intro a b
    obtain ⟨m, hm⟩ := hint a b
    by_cases ha : a = s <;> by_cases hb : b = s
    · refine ⟨m, ?_⟩; subst ha; subst hb; simp only [Pi.sub_apply]; linarith
    · refine ⟨m - 1, ?_⟩
      rw [ha] at hm
      simp only [Pi.sub_apply, Pi.single_apply, ha, hb, if_true, if_false]; push_cast; linarith
    · refine ⟨m + 1, ?_⟩
      rw [hb] at hm
      simp only [Pi.sub_apply, Pi.single_apply, ha, hb, if_true, if_false]; push_cast; linarith
    · refine ⟨m, ?_⟩
      simp only [Pi.sub_apply, Pi.single_apply, ha, hb, if_false]; linarith
  have h := Formalism.QuantumDeterminants.fdegRatio n (μ - Pi.single s 1) s hinj hint' (by rw [hadd]; exact hμ)
  rw [hadd] at h
  rw [← inv_div, h, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro s' hs'
  have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
  rw [inv_div]
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hne, if_false]
  congr 1 <;> ring

lemma prod_succ_div_nat_le_card_succ (S : Finset ℕ) : (∀ y ∈ S, 1 ≤ y) →
    ∏ y ∈ S, (((y : ℝ) + 1) / (y : ℝ)) ≤ (S.card : ℝ) + 1 := by
  refine Finset.induction_on_max S ?_ ?_
  · intro _
    simp
  · intro a S ha ih hS
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS]
    have hS' : ∀ y ∈ S, 1 ≤ y := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    have ih' := ih hS'
    have ha1 : 1 ≤ a := hS a (Finset.mem_insert_self a S)
    have hcard : S.card + 1 ≤ a := by
      have hsub : insert a S ⊆ Finset.Icc 1 a := by
        intro y hy
        rw [Finset.mem_Icc]
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact ⟨ha1, le_refl _⟩
        · exact ⟨hS y hy, (ha y hy').le⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, Finset.card_insert_of_notMem haS] at this
      omega
    have ha0 : (0:ℝ) < a := by exact_mod_cast ha1
    have hcardR : (S.card : ℝ) + 1 ≤ a := by exact_mod_cast hcard
    push_cast
    calc ((a:ℝ) + 1) / a * ∏ y ∈ S, (((y : ℝ) + 1) / (y : ℝ)) ≤ ((a:ℝ) + 1) / a * ((S.card : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ (S.card : ℝ) + 1 + 1 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ ha0]
          nlinarith

lemma prod_succ_div_injective_pos_bounds {ι : Type} (I : Finset ι) (y : ι → ℕ) (hinj : Set.InjOn y (I : Set ι)) (h1 : ∀ i ∈ I, 1 ≤ y i) :
    1 ≤ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) ∧ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) ≤ (I.card : ℝ) + 1 := by
  have himg : ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) = ∏ t ∈ I.image y, (((t : ℝ) + 1) / (t : ℝ)) :=
    by rw [Finset.prod_image (fun a ha b hb h => hinj ha hb h)]
  have hcard : (I.image y).card = I.card := Finset.card_image_of_injOn hinj
  constructor
  · calc (1:ℝ) = ∏ i ∈ I, (1:ℝ) := by simp
      _ ≤ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) := by
          refine Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i hi => ?_)
          have hy : (0:ℝ) < y i := by exact_mod_cast h1 i hi
          rw [le_div_iff₀ hy]
          linarith
  · rw [himg]
    have := prod_succ_div_nat_le_card_succ (I.image y) (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      exact h1 i hi)
    rw [hcard] at this
    exact this

lemma prod_succ_div_injective_int_bounds {ι : Type} (I : Finset ι) (x : ι → ℤ) (hinj : Set.InjOn x (I : Set ι)) (h0 : ∀ i ∈ I, x i ≠ 0)
    (h1 : ∀ i ∈ I, x i ≠ -1) :
    1 / ((I.card : ℝ) + 1) ≤ ∏ i ∈ I, (((x i : ℝ) + 1) / (x i : ℝ)) ∧
      ∏ i ∈ I, (((x i : ℝ) + 1) / (x i : ℝ)) ≤ (I.card : ℝ) + 1 := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not I (fun i => 0 < x i)
    (fun i => (((x i : ℝ) + 1) / (x i : ℝ)))
  have hPcard : (I.filter (fun i => 0 < x i)).card ≤ I.card := Finset.card_filter_le _ _
  have hQcard : (I.filter (fun i => ¬ 0 < x i)).card ≤ I.card := Finset.card_filter_le _ _
  have hPeq : ∏ i ∈ I.filter (fun i => 0 < x i), (((x i : ℝ) + 1) / (x i : ℝ)) =
      ∏ i ∈ I.filter (fun i => 0 < x i), ((((x i).toNat : ℕ) : ℝ) + 1) / (((x i).toNat : ℕ) : ℝ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hpos : 0 < x i := (Finset.mem_filter.mp hi).2
    have e : (((x i).toNat : ℕ) : ℝ) = (x i : ℝ) := by
      have := Int.toNat_of_nonneg hpos.le
      exact_mod_cast this
    rw [e]
  have injP : Set.InjOn (fun i => (x i).toNat) ((I.filter (fun i => 0 < x i) : Finset ι) : Set ι) := by
    intro i hi j hj hij
    have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
    have hij' : (x i).toNat = (x j).toNat := hij
    apply hinj hi'.1 hj'.1
    have e1 := Int.toNat_of_nonneg hi'.2.le
    have e2 := Int.toNat_of_nonneg hj'.2.le
    rw [← e1, ← e2, hij']
  have hPb := prod_succ_div_injective_pos_bounds (I.filter (fun i => 0 < x i)) (fun i => (x i).toNat) injP
    (fun i hi => by
      have := (Finset.mem_filter.mp hi).2
      omega)
  have hQeq : ∏ i ∈ I.filter (fun i => ¬ 0 < x i), (((x i : ℝ) + 1) / (x i : ℝ)) =
      (∏ i ∈ I.filter (fun i => ¬ 0 < x i),
        ((((-x i - 1).toNat : ℕ) : ℝ) + 1) / (((-x i - 1).toNat : ℕ) : ℝ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hq := Finset.mem_filter.mp hi
    have hxi0 := h0 i hq.1
    have hxi1 := h1 i hq.1
    have hle : x i ≤ -2 := by
      have := hq.2
      omega
    have e : (((-x i - 1).toNat : ℕ) : ℝ) = -(x i : ℝ) - 1 := by
      have := Int.toNat_of_nonneg (show 0 ≤ -x i - 1 by omega)
      have e' : (((-x i - 1).toNat : ℕ) : ℤ) = -x i - 1 := this
      have e'' : ((((-x i - 1).toNat : ℕ) : ℤ) : ℝ) = ((-x i - 1 : ℤ) : ℝ) := by rw [e']
      push_cast at e''
      exact e''
    rw [e, inv_div, show -(x i : ℝ) - 1 = -((x i : ℝ) + 1) by ring,
      show -((x i : ℝ) + 1) + 1 = -(x i : ℝ) by ring, neg_div_neg_eq]
  have injQ : Set.InjOn (fun i => (-x i - 1).toNat)
      ((I.filter (fun i => ¬ 0 < x i) : Finset ι) : Set ι) := by
    intro i hi j hj hij
    have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
    have hij' : (-x i - 1).toNat = (-x j - 1).toNat := hij
    apply hinj hi'.1 hj'.1
    have hi0 := h0 i hi'.1
    have hj0 := h0 j hj'.1
    have hi2 := hi'.2
    have hj2 := hj'.2
    omega
  have hQb := prod_succ_div_injective_pos_bounds (I.filter (fun i => ¬ 0 < x i)) (fun i => (-x i - 1).toNat) injQ
    (fun i hi => by
      have hq := Finset.mem_filter.mp hi
      have := h0 i hq.1
      have := h1 i hq.1
      have := hq.2
      omega)
  rw [← hsplit, hPeq, hQeq]
  obtain ⟨hP1, hP2⟩ := hPb
  obtain ⟨hQ1, hQ2⟩ := hQb
  have hPc : ((I.filter (fun i => 0 < x i)).card : ℝ) ≤ I.card := by exact_mod_cast hPcard
  have hQc : ((I.filter (fun i => ¬ 0 < x i)).card : ℝ) ≤ I.card := by exact_mod_cast hQcard
  set X := ∏ i ∈ I.filter (fun i => 0 < x i), ((((x i).toNat : ℕ) : ℝ) + 1) / (((x i).toNat : ℕ) : ℝ)
  set Y := ∏ i ∈ I.filter (fun i => ¬ 0 < x i),
    ((((-x i - 1).toNat : ℕ) : ℝ) + 1) / (((-x i - 1).toNat : ℕ) : ℝ)
  have hY0 : 0 < Y := by linarith
  have hYinv : Y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ1
  have hYinv0 : 0 ≤ Y⁻¹ := (inv_pos.mpr hY0).le
  have hN0 : (0:ℝ) < (I.card : ℝ) + 1 := by positivity
  constructor
  · have h1' : 1 / ((I.card : ℝ) + 1) ≤ Y⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hY0 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hP1 hYinv0]
  · nlinarith [mul_le_mul_of_nonneg_left hYinv (show (0:ℝ) ≤ X by linarith)]

lemma prod_shifted_ratio_bounds (n : ℕ) (μ : Fin n → ℝ) (s : Fin n) (hμ : Function.Injective μ)
    (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) (hinj : Function.Injective (μ + Pi.single s 1)) :
    1 / (n : ℝ) ≤ ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ∧
      ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ≤ n := by
  choose z hz using hint s
  have hcard : ((univ.erase s).card : ℝ) + 1 = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := Fin.pos s
    rw [Nat.cast_sub this, Nat.cast_one]
    ring
  have hz0 : ∀ s' ∈ univ.erase s, z s' ≠ 0 := by
    intro s' hs' h
    apply Finset.ne_of_mem_erase hs'
    apply hμ
    have := hz s'
    rw [h] at this
    push_cast at this
    linarith
  have hz1 : ∀ s' ∈ univ.erase s, z s' ≠ -1 := by
    intro s' hs' h
    have hne := Finset.ne_of_mem_erase hs'
    apply hne
    apply hinj
    have := hz s'
    rw [h] at this
    push_cast at this
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne]
    linarith
  have hzinj : Set.InjOn z ((univ.erase s : Finset (Fin n)) : Set (Fin n)) := by
    intro a _ b _ hab
    apply hμ
    have h1 := hz a
    have h2 := hz b
    rw [hab] at h1
    linarith
  have hc := prod_succ_div_injective_int_bounds (univ.erase s) z hzinj hz0 hz1
  have heq : ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') =
      ∏ s' ∈ univ.erase s, (((z s' : ℝ) + 1) / (z s' : ℝ)) := by
    refine Finset.prod_congr rfl (fun s' _ => ?_)
    rw [← hz s']
    ring
  rw [heq, ← hcard]
  exact hc

theorem degree_increment_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.DegStepBound := by
  intro n μ s hμ hint
  refine ⟨fun hinj => prod_shifted_ratio_bounds n μ s hμ hint hinj, fun hinj => ?_⟩
  have hμ' : Function.Injective (-μ) := fun a b h => hμ (neg_injective h)
  have hint' : ∀ a b, ∃ m : ℤ, (-μ) a - (-μ) b = (m : ℝ) := fun a b => by
    obtain ⟨m, hm⟩ := hint a b
    exact ⟨-m, by simp only [Pi.neg_apply]; push_cast; linarith⟩
  have hinj' : Function.Injective (-μ + Pi.single s 1) := by
    intro a b h
    apply hinj
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at h ⊢
    linarith
  have hb := prod_shifted_ratio_bounds n (-μ) s hμ' hint' hinj'
  have heq : ∏ s' ∈ univ.erase s, ((-μ) s + 1 - (-μ) s') / ((-μ) s - (-μ) s') =
      ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s') := by
    refine Finset.prod_congr rfl (fun s' _ => ?_)
    simp only [Pi.neg_apply]
    rw [show -μ s + 1 - -μ s' = -(μ s - 1 - μ s') by ring, show -μ s - -μ s' = -(μ s - μ s') by ring,
      neg_div_neg_eq]
  rw [heq] at hb
  exact hb

theorem degree_set_cardinality_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.DegSetBound := by
  intro n μ I hμ hint hgap
  classical
  have hanti : ∀ J : Finset (Fin n), StrictAnti (fun a => μ a + if a ∈ J then (1 : ℝ) else 0) := by
    intro J a b hab
    have := hgap a b hab
    show μ b + (if b ∈ J then (1 : ℝ) else 0) < μ a + if a ∈ J then (1 : ℝ) else 0
    split_ifs <;> linarith
  have hintJ : ∀ J : Finset (Fin n), ∀ a b, ∃ m : ℤ,
      (μ a + if a ∈ J then (1 : ℝ) else 0) - (μ b + if b ∈ J then (1 : ℝ) else 0) = (m : ℝ) := by
    intro J a b
    obtain ⟨m, hm⟩ := hint a b
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · exact ⟨m, by simp only [ha, hb, if_true]; linarith⟩
    · exact ⟨m + 1, by simp only [ha, hb, if_true, if_false]; push_cast; linarith⟩
    · exact ⟨m - 1, by simp only [ha, hb, if_true, if_false]; push_cast; linarith⟩
    · exact ⟨m, by simp only [ha, hb, if_false]; linarith⟩
  have fμ := Formalism.QuantumDeterminants.fdegPos n μ hμ.injective
  induction I using Finset.induction_on with
  | empty =>
    have : (fun a => μ a + if a ∈ (∅ : Finset (Fin n)) then (1 : ℝ) else 0) = μ := by
      funext a; simp
    rw [this, div_self fμ.ne']
    simp
  | insert s J hs ih =>
    have hstep : (fun a => μ a + if a ∈ insert s J then (1 : ℝ) else 0) =
        (fun a => μ a + if a ∈ J then (1 : ℝ) else 0) + Pi.single s 1 := by
      funext a
      by_cases ha : a = s
      · subst ha; simp [hs]
      · simp [ha]
    set ν : Fin n → ℝ := fun a => μ a + if a ∈ J then (1 : ℝ) else 0 with hν
    have fν := Formalism.QuantumDeterminants.fdegPos n ν (hanti J).injective
    have hinj' : Function.Injective (ν + Pi.single s 1) := by
      rw [← hstep]; exact (hanti _).injective
    have hr := Formalism.QuantumDeterminants.fdegRatio n ν s (hanti J).injective (hintJ J) hinj'
    have hb := (degree_increment_bound n ν s (hanti J).injective (hintJ J)).1 hinj'
    rw [← hr] at hb
    rw [hstep, Finset.card_insert_of_notMem hs]
    have hn : (0 : ℝ) < n := by
      have : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) s.2
      exact_mod_cast this
    have hprod : Formalism.QuantumDeterminants.fdegHC (ν + Pi.single s 1) / Formalism.QuantumDeterminants.fdegHC μ =
        (Formalism.QuantumDeterminants.fdegHC (ν + Pi.single s 1) / Formalism.QuantumDeterminants.fdegHC ν) * (Formalism.QuantumDeterminants.fdegHC ν / Formalism.QuantumDeterminants.fdegHC μ) := by
      field_simp
    rw [hprod]
    have hq0 : 0 ≤ Formalism.QuantumDeterminants.fdegHC ν / Formalism.QuantumDeterminants.fdegHC μ := (div_pos fν fμ).le
    constructor
    · rw [pow_succ, mul_inv, mul_comm]
      rw [one_div] at hb
      exact mul_le_mul hb.1 ih.1 (by positivity) (le_trans (by positivity) hb.1)
    · rw [pow_succ, mul_comm ((n : ℝ) ^ J.card)]
      exact mul_le_mul hb.2 ih.2 hq0 hn.le

end G5

section G6
open Finset

lemma le_exp_mul_of_near_bound (N D A δ c : ℝ) (hNA : N ≤ A) (hD : A - δ ≤ D) (hc : 0 < c) (hcA : c ≤ A) (hδ : 0 ≤ δ)
    (h2 : 2 * δ ≤ A) : N ≤ Real.exp (2 * δ / c) * D := by
  have hA : 0 < A := lt_of_lt_of_le hc hcA
  have hAd : 0 < A - δ := by linarith
  have hA0 : A ≠ 0 := hA.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have he : 1 + 2 * δ / c ≤ Real.exp (2 * δ / c) := by linarith [Real.add_one_le_exp (2 * δ / c)]
  have hdiv : 2 * δ / A ≤ 2 * δ / c := by
    have e : 2 * δ / c - 2 * δ / A = 2 * δ * (A - c) / (c * A) := by
      first
      | (field_simp; ring)
      | field_simp
    have : 0 ≤ 2 * δ * (A - c) / (c * A) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hc hA).le
    linarith
  have h3 : A ≤ (1 + 2 * δ / A) * (A - δ) := by
    have e : (1 + 2 * δ / A) * (A - δ) = A + δ - 2 * δ ^ 2 / A := by
      first
      | (field_simp; ring)
      | field_simp
    rw [e]
    have : 2 * δ ^ 2 / A ≤ δ := by
      rw [div_le_iff₀ hA]
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr h2)]
    linarith
  have hexpos : 0 ≤ Real.exp (2 * δ / c) := (Real.exp_pos _).le
  calc N ≤ A := hNA
    _ ≤ (1 + 2 * δ / A) * (A - δ) := h3
    _ ≤ Real.exp (2 * δ / c) * (A - δ) := mul_le_mul_of_nonneg_right (by linarith) hAd.le
    _ ≤ Real.exp (2 * δ / c) * D := mul_le_mul_of_nonneg_left hD hexpos

lemma paired_sum_exp_bound {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (I I' : Finset ι) (J : Finset κ) (N : ι → ℝ)
    (D t : κ → ℝ) (φ : ι → κ) (B : ℝ) (c : ℕ) (hsub : I' ⊆ I) (hφ : ∀ i ∈ I', φ i ∈ J)
    (hinj : Set.InjOn φ (I' : Set ι)) (hN : ∀ i ∈ I, 0 ≤ N i)
    (hp : ∀ i ∈ I', N i ≤ Real.exp (t (φ i)) * D (φ i)) (hB : ∀ i ∈ I \ I', N i ≤ B)
    (hB1 : 1 ≤ B) (hc : (I \ I').card ≤ c) (hD : ∀ a ∈ J, 1 ≤ D a) (ht : ∀ a ∈ J, 0 ≤ t a) :
    ∏ i ∈ I, N i ≤ B ^ c * Real.exp (∑ a ∈ J, t a) * ∏ a ∈ J, D a := by
  have e1 : ∏ i ∈ I, N i = (∏ i ∈ I \ I', N i) * ∏ i ∈ I', N i := (Finset.prod_sdiff hsub).symm
  have e2 : ∏ i ∈ I \ I', N i ≤ B ^ c := by
    calc ∏ i ∈ I \ I', N i ≤ ∏ _i ∈ I \ I', B :=
          Finset.prod_le_prod (fun i hi => hN i (Finset.sdiff_subset hi)) hB
      _ = B ^ (I \ I').card := by rw [Finset.prod_const]
      _ ≤ B ^ c := pow_le_pow_right₀ hB1 hc
  have h1 : ∀ a ∈ J, 1 ≤ Real.exp (t a) * D a := fun a ha =>
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (ht a ha)) (hD a ha)
  have him : I'.image φ ⊆ J := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hφ i hi
  have e3 : ∏ i ∈ I', N i ≤ ∏ a ∈ J, (Real.exp (t a) * D a) := by
    calc ∏ i ∈ I', N i ≤ ∏ i ∈ I', (Real.exp (t (φ i)) * D (φ i)) :=
          Finset.prod_le_prod (fun i hi => hN i (hsub hi)) hp
      _ = ∏ a ∈ I'.image φ, (Real.exp (t a) * D a) := (Finset.prod_image (f := fun a => Real.exp (t a) * D a) hinj).symm
      _ ≤ ∏ a ∈ J, (Real.exp (t a) * D a) :=
          Finset.prod_le_prod_of_subset_of_one_le him
            (fun a ha => le_trans zero_le_one (h1 a (him ha))) (fun a ha _ => h1 a ha)
  have e4 : ∏ a ∈ J, (Real.exp (t a) * D a) = Real.exp (∑ a ∈ J, t a) * ∏ a ∈ J, D a := by
    rw [Finset.prod_mul_distrib, Real.exp_sum]
  rw [e1, mul_assoc, ← e4]
  exact mul_le_mul e2 e3 (Finset.prod_nonneg fun i hi => hN i (hsub hi)) (by positivity)

lemma half_integer_neg_le_neg_half (y : ℝ) (z : ℤ) (h : y = (z : ℝ) + 1 / 2) (hy : y < 0) : y ≤ -(1 / 2) := by
  subst h
  have hz : z ≤ -1 := by
    by_contra hcon
    push_neg at hcon
    have h0 : (0:ℤ) ≤ z := by omega
    have : (0:ℝ) ≤ z := by exact_mod_cast h0
    linarith
  have : (z:ℝ) ≤ -1 := by exact_mod_cast hz
  linarith

lemma one_le_abs_of_int_ne_zero (y : ℝ) (z : ℤ) (h : y = (z : ℝ)) (hy : y ≠ 0) : 1 ≤ |y| := by
  subst h
  have hz : z ≠ 0 := by
    intro h0
    apply hy
    simp [h0]
  exact_mod_cast Int.one_le_abs hz

theorem first_operator_norm_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.supL2RatioMajorant := by
  intro k M lam mu u b bv ga q0 s hk hM hyp hreg
  obtain ⟨hlam, hlamZ, hluZ, hlu1, hlu2, hcloud, hnode, hlamb, hub, hgap, hga, hmuZ, hmu, hsum, hq1, hq2, hq3⟩ := hyp
  have hδ0 : ∀ a, 0 ≤ |mu a - lam a| := fun a => abs_nonneg _
  have hδq : ∀ a, |mu a - lam a| ≤ q0 := fun a =>
    le_trans (Finset.single_le_sum (f := fun a => |mu a - lam a|) (fun a _ => hδ0 a) (mem_univ a)) hsum
  have hq0 : 0 ≤ q0 := le_trans (hδ0 s) (hδq s)
  have hmu1 : ∀ a, mu a ≤ lam a + |mu a - lam a| := fun a => by
    have := le_abs_self (mu a - lam a); linarith
  have hmu2 : ∀ a, lam a - |mu a - lam a| ≤ mu a := fun a => by
    have := neg_abs_le (mu a - lam a); linarith
  have F1 : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) = (i : ℕ) → lam a + 1 / 2 ≤ u i := by
    intro i a h
    have e : a = Fin.castAdd M i := Fin.ext h
    obtain ⟨z, hz⟩ := hluZ a i
    have := half_integer_neg_le_neg_half _ z hz (by rw [e]; linarith [hlu1 i])
    linarith
  have F2 : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) + 1 = (i : ℕ) → u i + 1 / 2 ≤ lam a := by
    intro i a h
    have ha : (a : ℕ) < k := by have := i.isLt; omega
    have e : a = Fin.castAdd M ⟨(a : ℕ), ha⟩ := Fin.ext rfl
    obtain ⟨z, hz⟩ := hluZ a i
    have h1 : u i < lam a := by rw [e]; exact hlu2 ⟨(a : ℕ), ha⟩ i h
    have := half_integer_neg_le_neg_half (u i - lam a) (-z - 1) (by push_cast; linarith) (by linarith)
    linarith

  have hbv : 1 ≤ bv := by
    have h1 := hnode ⟨k - 1, by omega⟩ (by simp; omega)
    have h2 := hnode ⟨k, by omega⟩ (by simp)
    obtain ⟨z, hz⟩ := hlamZ ⟨k - 1, by omega⟩ ⟨k, by omega⟩
    have h3 : lam ⟨k, by omega⟩ < lam ⟨k - 1, by omega⟩ := hlam (by simp [Fin.lt_def]; omega)
    have h4 := one_le_abs_of_int_ne_zero _ z hz (by linarith)
    rw [abs_of_pos (by linarith)] at h4
    linarith [h1.2, h2.1]
  have hb : 1 ≤ b := by
    have h1 := hnode ⟨k, by omega⟩ (by simp)
    have h2 := abs_le.mp (hlamb ⟨k, by omega⟩)
    linarith [h1.2, h2.1]
  have hD : ∀ a ∈ univ.erase s, 1 ≤ |mu s - 1 - mu a| := by
    intro a ha
    have hne := Finset.ne_of_mem_erase ha
    obtain ⟨z1, hz1⟩ := hmuZ s
    obtain ⟨z2, hz2⟩ := hlamZ s a
    obtain ⟨z3, hz3⟩ := hmuZ a
    apply one_le_abs_of_int_ne_zero _ (z1 + z2 - z3 - 1) (by push_cast; linarith)
    exact sub_ne_zero.mpr (hreg a hne)
  have hN : ∀ i : Fin k, |mu s - 1 / 2 - u i| ≤ 4 * b := by
    intro i
    have h1 := abs_le.mp (hlamb s)
    have h2 := abs_le.mp (hub i)
    have h3 := hmu1 s
    have h4 := hmu2 s
    have h5 := hδq s
    rw [abs_le]; constructor <;> linarith
  have hDpos : 0 < ∏ a ∈ univ.erase s, |mu s - 1 - mu a| :=
    Finset.prod_pos fun a ha => lt_of_lt_of_le one_pos (hD a ha)
  have hsumle : ∀ c : ℝ, 0 < c → ∑ a ∈ univ.erase s, 2 * |mu a - lam a| / c ≤ 2 * q0 / c := by
    intro c hc
    calc ∑ a ∈ univ.erase s, 2 * |mu a - lam a| / c ≤ ∑ a, 2 * |mu a - lam a| / c :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => by positivity)
      _ = 2 * (∑ a, |mu a - lam a|) / c := by rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ 2 * q0 / c := by gcongr
  rw [div_le_iff₀ hDpos]
  by_cases hs : (s : ℕ) + 1 < k
  · rw [if_pos hs]
    have above : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) + 1 = (i : ℕ) → (i : ℕ) < (s : ℕ) →
        |mu s - 1 / 2 - u i| ≤ Real.exp (2 * |mu a - lam a| / (ga / 2)) * |mu s - 1 - mu a| := by
      intro i a hai his
      have g1 := hgap ⟨(i : ℕ), by have := i.isLt; omega⟩ s (by simp [Fin.lt_def]; exact his) hs
      have f1 := F1 i ⟨(i : ℕ), by have := i.isLt; omega⟩ rfl
      have f2 := F2 i a hai
      have h3 := hmu1 s
      have h5 := hδq s
      have h6 := hδq a
      have h7 := hmu2 a
      apply le_exp_mul_of_near_bound _ _ (lam a + 1 - mu s) _ _
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have := neg_le_abs (mu s - 1 - mu a); linarith
      · linarith
      · linarith
      · exact hδ0 a
      · linarith
    have below : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) = (i : ℕ) → (s : ℕ) + 2 ≤ (i : ℕ) →
        |mu s - 1 / 2 - u i| ≤ Real.exp (2 * |mu a - lam a| / (ga / 2)) * |mu s - 1 - mu a| := by
      intro i a hai his
      have g1 := hgap s ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ (by simp [Fin.lt_def]; omega)
        (by have := i.isLt; simp; omega)
      have f1 := F1 i a hai
      have f2 := F2 i ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ (by simp; omega)
      have h3 := hmu2 s
      have h5 := hδq s
      have h6 := hδq a
      have h7 := hmu1 a
      apply le_exp_mul_of_near_bound _ _ (mu s - 1 - lam a) _ _
      · rw [abs_of_nonneg (by linarith)]; linarith
      · have := le_abs_self (mu s - 1 - mu a); linarith
      · linarith
      · linarith
      · exact hδ0 a
      · linarith
    have key := paired_sum_exp_bound (univ : Finset (Fin k))
      (univ.filter fun i : Fin k => (1 ≤ (i : ℕ) ∧ (i : ℕ) < (s : ℕ)) ∨ (s : ℕ) + 2 ≤ (i : ℕ))
      (univ.erase s) (fun i => |mu s - 1 / 2 - u i|) (fun a => |mu s - 1 - mu a|)
      (fun a => 2 * |mu a - lam a| / (ga / 2))
      (fun i => ⟨if (i : ℕ) < (s : ℕ) then (i : ℕ) - 1 else (i : ℕ), by
        have := i.isLt; split_ifs <;> omega⟩) (4 * b) 3 (Finset.subset_univ _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        apply Finset.mem_erase.mpr ⟨?_, mem_univ _⟩
        intro e
        have e' := congrArg Fin.val e
        simp only at e'
        split_ifs at e' <;> omega)
      (by
        intro i hi j hj e
        have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        have e' := congrArg Fin.val e
        simp only at e'
        apply Fin.ext
        split_ifs at e' <;> omega)
      (fun i _ => abs_nonneg _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        by_cases c : (i : ℕ) < (s : ℕ)
        · apply above i _ _ c
          simp only [c, if_true]; omega
        · apply below i _ _ (by omega)
          simp only [c, if_false])
      (fun i _ => hN i) (by linarith)
      (by
        have hsub : (univ : Finset (Fin k)) \
            (univ.filter fun i : Fin k => (1 ≤ (i : ℕ) ∧ (i : ℕ) < (s : ℕ)) ∨ (s : ℕ) + 2 ≤ (i : ℕ)) ⊆
            {(⟨0, by omega⟩ : Fin k), ⟨(s : ℕ), by omega⟩, ⟨(s : ℕ) + 1, hs⟩} := by
          intro i hi
          have h := (Finset.mem_sdiff.mp hi).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          omega
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_three)
      hD (fun a _ => by positivity)
    have hS := hsumle (ga / 2) (by linarith)
    have hS2 : 2 * q0 / (ga / 2) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hexp : Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (ga / 2)) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (le_trans hS hS2)
    have hsq : 1 ≤ Real.sqrt k := by
      rw [Real.one_le_sqrt]; exact_mod_cast hk
    calc ∏ i, |mu s - 1 / 2 - u i|
        ≤ (4 * b) ^ 3 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (ga / 2)) *
          ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := key
      _ ≤ 64 * Real.exp 1 * Real.sqrt k * b ^ 3 * ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := by
          apply mul_le_mul_of_nonneg_right _ hDpos.le
          have h1 : (4 * b) ^ 3 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (ga / 2)) ≤
              (4 * b) ^ 3 * Real.exp 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
          have h2 : (4 * b) ^ 3 * Real.exp 1 * 1 ≤ (4 * b) ^ 3 * Real.exp 1 * Real.sqrt k :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          calc _ ≤ (4 * b) ^ 3 * Real.exp 1 * Real.sqrt k := by linarith
            _ = 64 * Real.exp 1 * Real.sqrt k * b ^ 3 := by ring
  · rw [if_neg hs]
    have above : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) + 1 = (i : ℕ) → (i : ℕ) + 1 < k →
        |mu s - 1 / 2 - u i| ≤ Real.exp (2 * |mu a - lam a| / (bv / 2)) * |mu s - 1 - mu a| := by
      intro i a hai hik
      have g1 := hcloud ⟨(i : ℕ), by have := i.isLt; omega⟩ hik
      have g2 := hnode s (by omega)
      have f1 := F1 i ⟨(i : ℕ), by have := i.isLt; omega⟩ rfl
      have f2 := F2 i a hai
      have h3 := hmu1 s
      have h5 := hδq s
      have h6 := hδq a
      have h7 := hmu2 a
      apply le_exp_mul_of_near_bound _ _ (lam a + 1 - mu s) _ _
      · rw [abs_of_nonpos (by linarith [g1.1, g2.2])]; linarith
      · have := neg_le_abs (mu s - 1 - mu a); linarith
      · linarith
      · linarith [g1.1, g2.2]
      · exact hδ0 a
      · linarith [g1.1, g2.2]
    have key := paired_sum_exp_bound (univ : Finset (Fin k))
      (univ.filter fun i : Fin k => 1 ≤ (i : ℕ) ∧ (i : ℕ) + 1 < k)
      (univ.erase s) (fun i => |mu s - 1 / 2 - u i|) (fun a => |mu s - 1 - mu a|)
      (fun a => 2 * |mu a - lam a| / (bv / 2))
      (fun i => ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩) (4 * b) 2 (Finset.subset_univ _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        apply Finset.mem_erase.mpr ⟨?_, mem_univ _⟩
        intro e
        have e' := congrArg Fin.val e
        simp only at e'
        omega)
      (by
        intro i hi j hj e
        have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        have e' := congrArg Fin.val e
        simp only at e'
        apply Fin.ext
        omega)
      (fun i _ => abs_nonneg _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        apply above i _ _ h.2
        simp only; omega)
      (fun i _ => hN i) (by linarith)
      (by
        have hsub : (univ : Finset (Fin k)) \
            (univ.filter fun i : Fin k => 1 ≤ (i : ℕ) ∧ (i : ℕ) + 1 < k) ⊆
            {(⟨0, by omega⟩ : Fin k), ⟨k - 1, by omega⟩} := by
          intro i hi
          have h := (Finset.mem_sdiff.mp hi).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          have := i.isLt
          omega
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_two)
      hD (fun a _ => by positivity)
    have hS := hsumle (bv / 2) (by linarith)
    have hS2 : 2 * q0 / (bv / 2) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hexp : Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (bv / 2)) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (le_trans hS hS2)
    calc ∏ i, |mu s - 1 / 2 - u i|
        ≤ (4 * b) ^ 2 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (bv / 2)) *
          ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := key
      _ ≤ 16 * Real.exp 1 * b ^ 2 * ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := by
          apply mul_le_mul_of_nonneg_right _ hDpos.le
          have h1 : (4 * b) ^ 2 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (bv / 2)) ≤
              (4 * b) ^ 2 * Real.exp 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
          calc _ ≤ (4 * b) ^ 2 * Real.exp 1 := h1
            _ = 16 * Real.exp 1 * b ^ 2 := by ring

end G6

section G8
open Finset

end G8

section G7
open Finset

end G7

end Formalism.HermitianLatticeCounting.P
