import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.productCup_of_system

section
variable {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)

private lemma rA_single_le {I : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hj : j ∈ I) :
    rA ℂ (xv x) {j} ≤ rA ℂ (xv x) I := by
  refine Algebra.adjoin_mono ?_
  rintro y ⟨i, hi, a, rfl⟩
  obtain rfl := Finset.mem_singleton.1 hi
  exact ⟨i, hj, a, rfl⟩

private lemma tmul_mem_tensorRing {I J : Finset (Fin (d + 1))} {a b : F} (ha : a ∈ rA ℂ (xv x) I)
    (hb : b ∈ rA ℂ (xv x) J) : a ⊗ₜ[ℂ] b ∈ R0 x I J :=
  ⟨(⟨a, ha⟩ : rA ℂ (xv x) I) ⊗ₜ[ℂ] (⟨b, hb⟩ : rA ℂ (xv x) J), by
    simp [Algebra.TensorProduct.map_tmul]⟩

private abbrev PP (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) : Submodule ℂ (F ⊗[ℂ] F) :=
  sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (Set.range (f0 x j))

private lemma f_mul_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} {t m : F ⊗[ℂ] F}
    (ht : t ∈ Set.range (f0 x j)) (hm : m ∈ R0 x I J) : t * m ∈ PP x I J j := by
  have h : (Subalgebra.toSubmodule (R0 x I J)).map (Algebra.lmul ℂ (F ⊗[ℂ] F) t) ≤ PP x I J j :=
    le_iSup₂ (f := fun r (_ : r ∈ Set.range (f0 x j)) =>
      (Subalgebra.toSubmodule (R0 x I J)).map (Algebra.lmul ℂ (F ⊗[ℂ] F) r)) t ht
  exact h ⟨m, hm, rfl⟩

private lemma mul_mem_PP {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} {r p : F ⊗[ℂ] F}
    (hr : r ∈ R0 x I J) (hp : p ∈ PP x I J j) : r * p ∈ PP x I J j := by
  have h : PP x I J j ≤ (PP x I J j).comap (LinearMap.mulLeft ℂ r) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨m, hm, rfl⟩
    show r * (t * m) ∈ PP x I J j
    rw [mul_left_comm]
    exact f_mul_mem x ht ((R0 x I J).mul_mem hr hm)
  exact h hp

private lemma diff_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hI : j ∈ I) (hJ : j ∈ J) {a : F}
    (ha : a ∈ rA ℂ (xv x) {j}) : a ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] a ∈ PP x I J j := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, a, rfl⟩ := hy
    obtain rfl := Finset.mem_singleton.1 hi
    by_cases hne : a = i
    · subst hne
      simp
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hne
      have := f_mul_mem x (I := I) (J := J) (j := i) ⟨l, rfl⟩ (one_mem _)
      simpa [f0] using this
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]
    exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (a + b) ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] (a + b) =
        (a ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] a) + (b ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] b) := by
      rw [TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
    rw [e]
    exact add_mem ha hb
  | mul a b ha' hb' ha hb =>
    have e : (a * b) ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] (a * b) =
        (a ⊗ₜ[ℂ] (1 : F)) * (b ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] b) +
          ((1 : F) ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] a) := by
      simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm b a]
      abel
    rw [e]
    exact add_mem (mul_mem_PP x (tmul_mem_tensorRing x (rA_single_le x hI ha') (one_mem _)) hb)
      (mul_mem_PP x (tmul_mem_tensorRing x (one_mem _) (rA_single_le x hJ hb')) ha)

private lemma diag_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hI : j ∈ I) (hJ : j ∈ J)
    (w : rA ℂ (xv x) {j} ⊗[ℂ] rA ℂ (xv x) {j}) :
    Algebra.TensorProduct.map (rA ℂ (xv x) {j}).val (rA ℂ (xv x) {j}).val w -
      (1 : F) ⊗ₜ[ℂ] Algebra.TensorProduct.lmul' ℂ
        (Algebra.TensorProduct.map (rA ℂ (xv x) {j}).val (rA ℂ (xv x) {j}).val w) ∈ PP x I J j := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have e : (a : F) ⊗ₜ[ℂ] (b : F) - (1 : F) ⊗ₜ[ℂ] ((a : F) * b) =
        ((1 : F) ⊗ₜ[ℂ] (b : F)) * ((a : F) ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] (a : F)) := by
      simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm (b : F) (a : F)]
    simp only [Algebra.TensorProduct.map_tmul, Subalgebra.coe_val, Algebra.TensorProduct.lmul'_apply_tmul]
    rw [e]
    exact mul_mem_PP x (tmul_mem_tensorRing x (one_mem _) (rA_single_le x hJ b.2)) (diff_mem x hI hJ a.2)
  | add a b ha hb =>
    have := add_mem ha hb
    simp only [map_add, TensorProduct.tmul_add]
    convert this using 1
    abel

private lemma prod_mem_single (I : Finset (Fin (d + 1))) (j : Fin (d + 1)) :
    (∏ i ∈ I, (x i : F) / x j) ∈ rA ℂ (xv x) {j} :=
  prod_mem fun i _ => Algebra.subset_adjoin ⟨j, Finset.mem_singleton_self j, i, rfl⟩

private lemma pow_mul_mem (I : Finset (Fin (d + 1))) (j : Fin (d + 1)) {a : F} (ha : a ∈ rA ℂ (xv x) I) :
    ∃ N : ℕ, (∏ i ∈ I, (x i : F) / x j) ^ N * a ∈ rA ℂ (xv x) {j} := by
  have hs := prod_mem_single x I j
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, b, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have e : (∏ i ∈ I, (x i : F) / x j) ^ 1 * (xv x b / xv x i) =
        (∏ i' ∈ I.erase i, (x i' : F) / x j) * ((x b : F) / x j) := by
      rw [pow_one, ← Finset.mul_prod_erase I _ hi]
      have h1 : (x i : F) ≠ 0 := (x i).ne_zero
      have h2 : (x j : F) ≠ 0 := (x j).ne_zero
      simp only [xv]
      field_simp
    rw [e]
    exact mul_mem (prod_mem_single x _ j) (Algebra.subset_adjoin ⟨j, Finset.mem_singleton_self j, b, rfl⟩)
  | algebraMap c => exact ⟨0, by simpa using (rA ℂ (xv x) {j}).algebraMap_mem c⟩
  | add a b _ _ ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨N', hN'⟩ := hb
    refine ⟨N + N', ?_⟩
    have e : (∏ i ∈ I, (x i : F) / x j) ^ (N + N') * (a + b) =
        (∏ i ∈ I, (x i : F) / x j) ^ N' * ((∏ i ∈ I, (x i : F) / x j) ^ N * a) +
          (∏ i ∈ I, (x i : F) / x j) ^ N * ((∏ i ∈ I, (x i : F) / x j) ^ N' * b) := by
      rw [pow_add]; ring
    rw [e]
    exact add_mem (mul_mem (pow_mem hs _) hN) (mul_mem (pow_mem hs _) hN')
  | mul a b _ _ ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨N', hN'⟩ := hb
    refine ⟨N + N', ?_⟩
    have e : (∏ i ∈ I, (x i : F) / x j) ^ (N + N') * (a * b) =
        ((∏ i ∈ I, (x i : F) / x j) ^ N * a) * ((∏ i ∈ I, (x i : F) / x j) ^ N' * b) := by
      rw [pow_add]; ring
    rw [e]
    exact mul_mem hN hN'

private lemma inv_prod_mem {I : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hj : j ∈ I) :
    (∏ i ∈ I, (x j : F) / x i) ∈ rA ℂ (xv x) I :=
  prod_mem fun i hi => Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

private lemma prod_mul_inv (I : Finset (Fin (d + 1))) (j : Fin (d + 1)) :
    (∏ i ∈ I, (x j : F) / x i) * (∏ i ∈ I, (x i : F) / x j) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have h1 : (x i : F) ≠ 0 := (x i).ne_zero
  have h2 : (x j : F) ≠ 0 := (x j).ne_zero
  field_simp

private lemma scale_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} (w : rA ℂ (xv x) I ⊗[ℂ] rA ℂ (xv x) J) :
    ∃ N : ℕ, ((∏ i ∈ I, (x i : F) / x j) ⊗ₜ[ℂ] (∏ i ∈ J, (x i : F) / x j)) ^ N *
      Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val w ∈ R0 x {j} {j} := by
  have hs := prod_mem_single x I j
  have ht := prod_mem_single x J j
  have hst := tmul_mem_tensorRing x hs ht
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨N, hN⟩ := pow_mul_mem x I j a.2
    obtain ⟨N', hN'⟩ := pow_mul_mem x J j b.2
    refine ⟨N + N', ?_⟩
    have e : ((∏ i ∈ I, (x i : F) / x j) ⊗ₜ[ℂ] (∏ i ∈ J, (x i : F) / x j)) ^ (N + N') *
        Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val (a ⊗ₜ[ℂ] b) =
        (((∏ i ∈ I, (x i : F) / x j) ^ N') ⊗ₜ[ℂ] ((∏ i ∈ J, (x i : F) / x j) ^ N)) *
          (((∏ i ∈ I, (x i : F) / x j) ^ N * (a : F)) ⊗ₜ[ℂ] ((∏ i ∈ J, (x i : F) / x j) ^ N' * (b : F))) := by
      simp only [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val,
        Algebra.TensorProduct.tmul_mul_tmul, pow_add]
      congr 1 <;> ring
    rw [e]
    exact (R0 x {j} {j}).mul_mem (tmul_mem_tensorRing x (pow_mem hs _) (pow_mem ht _)) (tmul_mem_tensorRing x hN hN')
  | add a b ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨N', hN'⟩ := hb
    refine ⟨N + N', ?_⟩
    rw [map_add, mul_add, pow_add]
    refine add_mem ?_ ?_
    · rw [mul_comm (_ ^ N), mul_assoc]
      exact (R0 x {j} {j}).mul_mem (pow_mem hst _) hN
    · rw [mul_assoc]
      exact (R0 x {j} {j}).mul_mem (pow_mem hst _) hN'

end

theorem kernelZero_holds :
    Ker0 := by
  intro F _ _ d x _ I J j hI hJ m hm h0
  obtain ⟨w, rfl⟩ := hm
  obtain ⟨N, hN⟩ := scale_mem x (j := j) w
  set m := Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val w with hm
  set c := (∏ i ∈ I, (x i : F) / x j) ⊗ₜ[ℂ] (∏ i ∈ J, (x i : F) / x j) with hc
  set u := (∏ i ∈ I, (x j : F) / x i) ⊗ₜ[ℂ] (∏ i ∈ J, (x j : F) / x i) with hu
  have huR : u ∈ R0 x I J := tmul_mem_tensorRing x (inv_prod_mem x hI) (inv_prod_mem x hJ)
  have huc : u * c = 1 := by
    rw [hu, hc, Algebra.TensorProduct.tmul_mul_tmul, prod_mul_inv, prod_mul_inv]
    rfl
  obtain ⟨w', hw'⟩ := hN
  have h1 := diag_mem x hI hJ w'
  have hz : Algebra.TensorProduct.lmul' ℂ (c ^ N * m) = 0 := by
    have h0' : Algebra.TensorProduct.lmul' ℂ m = 0 := h0
    rw [map_mul, h0', mul_zero]
  have h2 : c ^ N * m ∈ PP x I J j := by
    have e : Algebra.TensorProduct.map (rA ℂ (xv x) {j}).val (rA ℂ (xv x) {j}).val w' = c ^ N * m := hw'
    rw [e, hz] at h1
    simpa using h1
  have h3 := mul_mem_PP x (pow_mem huR N) h2
  rwa [← mul_assoc, ← mul_pow, huc, one_pow, one_mul] at h3

end UpperTheory.Gal.productCup_of_system

end
