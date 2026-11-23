import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransform

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem inv_small {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g : A) (α β : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) :
    ∃ w ∈ Algebra.adjoin O ({g} : Set A), (algebraMap O A α + algebraMap O A β * g) * w = 1 := by
  obtain ⟨Q, hQm, hQ⟩ := hg
  rw [← aeval_def] at hQ
  set D := algebraMap O A α + algebraMap O A β * g with hD
  set n := Q.natDegree
  let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (X - C α) ^ i * C β ^ (n - i)
  have hR : aeval D R = 0 := by
    have : aeval D R = algebraMap O A β ^ n * aeval g Q := by
      conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
      simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Algebra.smul_def, hD]
      have : algebraMap O A β ^ n = algebraMap O A β ^ i * algebraMap O A β ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hin]
      rw [this]; ring
    rw [this, hQ, mul_zero]
  have hR0 : IsUnit (R.eval 0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hb : IsLocalRing.residue O β = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hβ
    have ha : IsLocalRing.residue O α ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hα
    simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, map_sum, map_mul, map_pow,
      map_sub, map_zero, hb]
    rw [Finset.sum_eq_single n]
    · simp [n, hQm.coeff_natDegree, ha]
    · intro i hi hin
      have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
      rw [zero_pow this.ne', mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  obtain ⟨w, hw, hDw⟩ := sub_inv_mem D 0 R hR hR0
  rw [map_zero, sub_zero] at hDw
  refine ⟨w, ?_, hDw⟩
  have hDmem : D ∈ Algebra.adjoin O ({g} : Set A) :=
    add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hDmem) hw

theorem adjoin_both {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g Y : A) (α β γ : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) (hγ : IsUnit γ)
    (hY : Y * (algebraMap O A α + algebraMap O A β * g) = algebraMap O A γ * g) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  obtain ⟨w, hw, hDw⟩ := inv_small g α β hg hα hβ
  have h1 : Y ∈ Algebra.adjoin O ({g} : Set A) := by
    have e : Y = algebraMap O A γ * g * w := by linear_combination (-Y) * hDw + w * hY
    rw [e]
    exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hw
  refine ⟨h1, ?_⟩
  have hYi : IsIntegral O Y := IsIntegral.of_mem_of_fg _ hg.fg_adjoin_singleton Y h1
  have hβ' : -β ∈ IsLocalRing.maximalIdeal O := neg_mem hβ
  obtain ⟨v, hv, hEv⟩ := inv_small Y γ (-β) hYi hγ hβ'
  have e : g = algebraMap O A α * Y * v := by
    rw [map_neg] at hEv
    linear_combination (-g) * hEv - v * hY
  rw [e]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hv

variable {K : UQ}

theorem congruence_selfadj (B : InvAlg K) (a x y : K.O) (ha0 : a ≠ 0)
    (hac : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hu : (1 + algebraMap K.O B.A a * B.g) * B.σ (1 + algebraMap K.O B.A a * B.g) = 1)
    (Y w : B.A)
    (hw : (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) * w = 1)
    (hY : Y * (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) =
      algebraMap K.O B.A (x * y) * B.g) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have sa : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [σ_algebraMap, hac, ← IsScalarTower.algebraMap_apply]
  have h1 := congrArg B.σ hY
  simp only [map_mul, map_sub, map_add, sx, sy, sa] at h1 hY hw
  rw [map_add, map_one, map_mul, sa] at hu
  set G := B.g
  set S := B.σ B.g
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  set aA := algebraMap K.O B.A a
  have key : (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA = 0 := by
    linear_combination (-aA * (1 + aA * G)) * h1 - (xA * yA - aA * B.σ Y * yA) * hu - aA * hY
  have key2 : (B.σ Y - Y) * aA = 0 := by
    calc (B.σ Y - Y) * aA = (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA * w := by
          linear_combination (-(B.σ Y - Y) * aA) * hw
      _ = 0 := by rw [key, zero_mul]
  have hae : algebraMap K.O K.E a ≠ 0 := by
    intro h; exact ha0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  have : (algebraMap K.O K.E a) • (B.σ Y - Y) = 0 := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_comm]; exact key2
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left hae)

end GlobalTheory.UnitLemma.CongruenceCayley

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a →
    ∀ B₁ B₂ : InvAlg K,
    (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 →
    (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  intro hL K a ha B₁ B₂ hu₁ hu₂ hsep
  by_cases hint : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  swap
  · obtain ⟨h1, h2⟩ := kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral K B₁ B₂ hint
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]
  obtain ⟨i₁, i₂⟩ := hint
  obtain ⟨ha0, ham, hac⟩ := ha
  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (CayleyAny.isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := CayleyAny.isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hβ : x * a ∈ IsLocalRing.maximalIdeal K.O := Ideal.mul_mem_left _ _ ham
  have hγ : IsUnit (x * y) := hxu.mul hyu
  obtain ⟨w₁, -, hw₁⟩ := inv_small B₁.g (x - y) (x * a) i₁ hxyu hβ
  obtain ⟨w₂, -, hw₂⟩ := inv_small B₂.g (x - y) (x * a) i₂ hxyu hβ
  set Y₁ := algebraMap K.O B₁.A (x * y) * B₁.g * w₁ with hY₁d
  set Y₂ := algebraMap K.O B₂.A (x * y) * B₂.g * w₂ with hY₂d
  have hY₁ : Y₁ * (algebraMap K.O B₁.A (x - y) + algebraMap K.O B₁.A (x * a) * B₁.g) =
      algebraMap K.O B₁.A (x * y) * B₁.g := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A (x * y) * B₁.g) * hw₁
  have hY₂ : Y₂ * (algebraMap K.O B₂.A (x - y) + algebraMap K.O B₂.A (x * a) * B₂.g) =
      algebraMap K.O B₂.A (x * y) * B₂.g := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A (x * y) * B₂.g) * hw₂
  have adj₁ := adjoin_both B₁.g Y₁ (x - y) (x * a) (x * y) i₁ hxyu hβ hγ hY₁
  have adj₂ := adjoin_both B₂.g Y₂ (x - y) (x * a) (x * y) i₂ hxyu hβ hγ hY₂
  have iP : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := IsIntegral.pair i₁ i₂
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * (algebraMap K.O (B₁.A × B₂.A) (x - y) +
      algebraMap K.O (B₁.A × B₂.A) (x * a) * (B₁.g, B₂.g)) =
      algebraMap K.O (B₁.A × B₂.A) (x * y) * (B₁.g, B₂.g) :=
    Prod.ext hY₁ hY₂
  have adjP := adjoin_both ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) (x - y) (x * a) (x * y) iP hxyu hβ hγ hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := congruence_selfadj B₁ a x y ha0 hac hxy hu₁ Y₁ w₁ hw₁ hY₁
  have sa₂ := congruence_selfadj B₂ a x y ha0 hac hxy hu₂ Y₂ w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g i₁
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g i₂
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CongruenceCayley
