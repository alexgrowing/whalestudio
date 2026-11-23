import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

namespace GlobalTheory.Hk3.HoweDuality.Reps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eventually_pow_mul_le_one (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (e : L) : ∀ᶠ K : ℕ in Filter.atTop, Valued.v ϖ ^ K * Valued.v e ≤ 1 := by
  rcases eq_or_ne (Valued.v e) 0 with h0 | h0
  · exact Filter.Eventually.of_forall fun K => by rw [h0, mul_zero]; exact zero_le
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    refine Filter.eventually_atTop.2 ⟨(Multiplicative.toAdd m).toNat, fun K hK => ?_⟩
    rw [← hm, hϖ, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe,
      ← ofAdd_nsmul, ← Multiplicative.toAdd_le]
    simp only [toAdd_mul, toAdd_ofAdd, toAdd_one, nsmul_eq_mul, mul_neg, mul_one]
    have : Multiplicative.toAdd m ≤ (K : ℤ) := (Int.self_le_toNat _).trans (by exact_mod_cast hK)
    linarith

end GlobalTheory.Hk3.HoweDuality.Reps

open GlobalTheory.Hk3.HoweDuality.Reps in
theorem GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (n n' : ℕ) (a : GL (Fin n) L) (x : Matrix (Fin n') (Fin n) L),
  (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ y ∈ Y, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
  intro L _ _ ϖ hϖ hR n n' a x hx
  classical
  set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai
  have hinv : ai * (a : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [hai, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  obtain ⟨K, hK⟩ := (Filter.eventually_all.2 fun p : Fin n × Fin n =>
    eventually_pow_mul_le_one ϖ hϖ (ai p.1 p.2)).exists
  obtain ⟨R, hRint, hRapp⟩ := hR K
  have hv1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]; simp

  let S : Finset (Matrix (Fin n') (Fin n) L) :=
    Fintype.piFinset fun _ : Fin n' => Fintype.piFinset fun _ : Fin n => R
  have hSint : ∀ s ∈ S, ∀ i j, s i j ∈ Formalism.UG.intL L := by
    intro s hs i j
    exact hRint _ (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hs i) j)

  have hcong : ∀ d : Matrix (Fin n') (Fin n) L, (∀ i j, Valued.v (d i j) ≤ Valued.v ϖ ^ K) →
      d * ai ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
    intro d hd i j
    rw [Matrix.mul_apply]
    refine (Formalism.UG.intL L).sum_mem fun k _ => ?_
    change Valued.v (d i k * ai k j) ≤ 1
    rw [map_mul]
    calc Valued.v (d i k) * Valued.v (ai k j) ≤ Valued.v ϖ ^ K * Valued.v (ai k j) := by gcongr; exact hd i k
      _ ≤ 1 := hK (k, j)
  let T : Finset (Matrix (Fin n') (Fin n) L) := insert x (S.image fun s => s * ai)
  have hTint : ∀ t ∈ T, ∀ i j, (t * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hx
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
      rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
      exact hSint s hs
  let q : Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n :=
    QuotientAddGroup.mk
  let rep : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n → Matrix (Fin n') (Fin n) L :=
    fun c => if q x = c then x else if h : ∃ t ∈ T, q t = c then h.choose else 0
  have hrep : ∀ t ∈ T, rep (q t) ∈ T ∧ q (rep (q t)) = q t := by
    intro t ht
    by_cases hxt : q x = q t
    · have hr : rep (q t) = x := by simp [rep, hxt]
      rw [hr]; exact ⟨Finset.mem_insert_self _ _, hxt⟩
    · have h : ∃ t' ∈ T, q t' = q t := ⟨t, ht, rfl⟩
      simp only [rep, hxt, if_false, h, dif_pos]
      exact h.choose_spec
  refine ⟨T.image fun t => rep (q t), ?_, ?_, ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨x, Finset.mem_insert_self _ _, ?_⟩
    simp [rep]
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact hTint _ (hrep t ht).1
  · intro y hy y' hy' hyy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hy'
    have e : q t = q t' := by
      rw [← (hrep t ht).2, ← (hrep t' ht').2]
      exact QuotientAddGroup.eq_iff_sub_mem.2 hyy
    rw [e]
  · intro u hu
    have hpick : ∀ i j, ∃ r ∈ R, Valued.v (u i j - r) ≤ Valued.v ϖ ^ K := fun i j => hRapp _ (hu i j)
    choose s hsR hsv using hpick
    have hsS : (Matrix.of fun i j => s i j) ∈ S := by
      refine Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => hsR i j
    have ht : (Matrix.of fun i j => s i j) * ai ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hsS)
    refine ⟨rep (q ((Matrix.of fun i j => s i j) * ai)), Finset.mem_image_of_mem _ ht, ?_⟩
    have h1 : u * ai - (Matrix.of fun i j => s i j) * ai ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
      rw [← Matrix.sub_mul]
      exact hcong _ fun i j => by simpa using hsv i j
    have h2 := (hrep _ ht).2
    rw [← QuotientAddGroup.eq_iff_sub_mem] at h1 ⊢
    exact h1.trans h2.symm
