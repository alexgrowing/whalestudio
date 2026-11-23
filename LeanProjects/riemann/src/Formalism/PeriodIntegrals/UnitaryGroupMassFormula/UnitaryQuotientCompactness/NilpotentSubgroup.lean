import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SBasic

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ}

def NC (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0

lemma mem_Nset_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ NC k r g := by
  simp only [Nset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hU, h2, h3⟩
    refine ⟨hU, fun i j hj hi => ?_⟩
    by_cases hjr : j.val < r
    · have hej : eI k r ⟨j.val, hjr⟩ = j := Fin.ext (by simp [eI])
      have h := h2 ⟨j.val, hjr⟩ i (by rw [min_eq_left hjr.le] at hi; exact hi)
      rwa [hej] at h
    · push_neg at hjr
      exact h3 i j hjr hj (by rwa [min_eq_right hjr] at hi)
  · rintro ⟨hU, hN⟩
    refine ⟨hU, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    · have hv : (eI k r a).val = a.val := by simp [eI]
      exact hN i (eI k r a) (by rw [hv]; omega) (by rw [hv, min_eq_left a.isLt.le]; exact hai)
    · exact hN i j hj2 (by rw [min_eq_right hj1]; exact hi)

lemma nc_one : NC k r (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
  intro i j _ _
  rw [Matrix.one_apply]

lemma nc_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : NC k r a) (hb : NC k r b) : NC k r (a * b) := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hb j j hj (min_le_left _ _), if_pos rfl, mul_one]
    exact ha i j hj hi
  · intro l _ hlj
    by_cases hl : min j.val r ≤ l.val
    · rw [hb l j hj hl, if_neg hlj, mul_zero]
    · push_neg at hl
      have hlr : l.val < r := lt_of_lt_of_le hl (min_le_right _ _)
      have h := ha i l (by omega) (by rw [min_eq_left hlr.le]; omega)
      rw [h, if_neg (by intro h'; rw [h'] at hi; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma mul_apply_eq_ite_of_lower_block_scalar {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : NC k r a) (c : ℂ)
    {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
      x i j = if i = j then c else 0) :
    ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
      (x * a) i j = if i = j then c else 0 := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [ha j j hj (min_le_left _ _), if_pos rfl, mul_one]
    exact hx i j hj hi
  · intro l _ hlj
    by_cases hl : min j.val r ≤ l.val
    · rw [ha l j hj hl, if_neg hlj, mul_zero]
    · push_neg at hl
      have hlr : l.val < r := lt_of_lt_of_le hl (min_le_right _ _)
      have h := hx i l (by omega) (by rw [min_eq_left hlr.le]; omega)
      rw [h, if_neg (by intro h'; rw [h'] at hi; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma nc_inv {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) (ha : NC k r a) : NC k r a⁻¹ := by
  have hfix := mul_apply_eq_ite_of_lower_block_scalar (k := k) (r := r) (a := a) ha
  let V : Submodule ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    { carrier := {x | ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
          x i j = if i = j then x 0 0 else 0}
      add_mem' := by
        intro x y hx hy i j hj hi
        simp only [Set.mem_setOf_eq] at hx hy
        rw [Matrix.add_apply, hx i j hj hi, hy i j hj hi, Matrix.add_apply]
        split_ifs <;> simp
      zero_mem' := by
        intro i j _ _
        simp
      smul_mem' := by
        intro c x hx i j hj hi
        simp only [Set.mem_setOf_eq] at hx
        rw [Matrix.smul_apply, hx i j hj hi, Matrix.smul_apply]
        split_ifs <;> simp }
  have hV : ∀ x ∈ V, LinearMap.mulRight ℂ a x ∈ V := by
    intro x hx i j hj hi
    have h00 : (x * a) 0 0 = x 0 0 := by
      rw [hfix (x 0 0) hx 0 0 (by simp) (by simp), if_pos rfl]
    show (x * a) i j = if i = j then (x * a) 0 0 else 0
    rw [h00]
    exact hfix (x 0 0) hx i j hj hi
  let f : V →ₗ[ℂ] V := (LinearMap.mulRight ℂ a).restrict hV
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a = y * a := congrArg Subtype.val hxy
    have h2 := congrArg (· * a⁻¹) h1
    simp only [Matrix.mul_assoc, mul_inv_UH hU, Matrix.mul_one] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have h1V : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ V := by
    intro i j _ _
    simp [Matrix.one_apply]
  obtain ⟨x, hx⟩ := hsurj ⟨1, h1V⟩
  have hxa : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a = 1 := congrArg Subtype.val hx
  have hxinv : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = a⁻¹ := by
    calc (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = x * (a * a⁻¹) := by rw [mul_inv_UH hU, Matrix.mul_one]
      _ = (x * a) * a⁻¹ := by rw [Matrix.mul_assoc]
      _ = a⁻¹ := by rw [hxa, Matrix.one_mul]
  have hc : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) 0 0 = 1 := by
    have h := hfix ((x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) 0 0) x.2 0 0 (by simp) (by simp)
    rw [hxa, if_pos rfl, Matrix.one_apply_eq] at h
    exact h.symm
  intro i j hj hi
  rw [← hxinv]
  have h := x.2 i j hj hi
  rw [hc] at h
  exact h

theorem nilpotent_subgroup : NGroup := by
  intro k r
  refine ⟨(mem_Nset_iff 1).2 ⟨one_mem_UH, nc_one⟩, fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨haU, haN⟩ := (mem_Nset_iff a).1 ha
    obtain ⟨hbU, hbN⟩ := (mem_Nset_iff b).1 hb
    exact (mem_Nset_iff _).2 ⟨mul_mem_UH haU hbU, nc_mul haN hbN⟩
  · obtain ⟨haU, haN⟩ := (mem_Nset_iff a).1 ha
    exact (mem_Nset_iff _).2 ⟨inv_mem_UH haU, nc_inv haU haN⟩

lemma inv_inv_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r)) :
    a⁻¹⁻¹ = a := Matrix.nonsing_inv_nonsing_inv a (Matrix.isUnit_det_of_right_inverse (mul_inv_UH hU))

lemma n_ut {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r)
    (i j : Fin (2 * r + k + 1)) (hij : j.val ≤ i.val) : n i j = if i = j then 1 else 0 := by
  obtain ⟨hU, hN⟩ := (mem_Nset_iff n).1 hn
  by_cases hj : j.val ≤ r + k
  · exact hN i j hj (le_trans (min_le_left _ _) hij)
  · push_neg at hj
    have hinv : NC k r n⁻¹ := nc_inv hU hN
    have hvj : (piI k r j).val = 2 * r + k - j.val := by
      rw [piI_val, if_neg (by omega)]
    have hvi : (piI k r i).val = 2 * r + k - i.val := by
      rw [piI_val, if_neg (by omega)]
    have h1 := hinv (piI k r j) (piI k r i) (by omega)
      (by rw [hvi, hvj, min_eq_left (by omega)]; omega)
    rw [inv_eq_UH hU, Hpk_mul_mul_Hpk_apply, piI_piI, piI_piI, conjTranspose_apply] at h1
    have he1 : epsI k r (piI k r j) = 1 := by
      simp only [epsI]; rw [if_neg (by omega)]
    have he2 : epsI k r (piI k r i) = 1 := by
      simp only [epsI]; rw [if_neg (by omega)]
    rw [he1, he2, one_mul, mul_one] at h1
    have h2 := congrArg star h1
    rw [star_star] at h2
    rw [h2]
    by_cases hij' : i = j
    · subst hij'
      simp
    · have hne : piI k r j ≠ piI k r i := by
        intro h
        have h' := congrArg (piI k r) h
        rw [piI_piI, piI_piI] at h'
        exact hij' h'.symm
      rw [if_neg hne, if_neg hij', star_zero]

end PI.QuotSetU.UnitaryGroupMassFormula.SW
