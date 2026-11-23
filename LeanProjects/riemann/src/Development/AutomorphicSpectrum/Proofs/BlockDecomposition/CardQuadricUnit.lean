import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCount
open Matrix

namespace GlobalTheory.CompanionTheory.SW.QuadricUnit

open GlobalTheory.CompanionTheory.SW.QuadricCount

theorem char_sum {k α : Type} [AddCommGroup k] (ψ : AddChar k ℂ) (s : Finset α) (f : α → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

section OneVar

variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

theorem sum_sq_eq (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c : k} (hc : c ≠ 0) :
    ∑ y : k, ψ (c * (y * y)) = ∑ z : k, (quadraticChar k z : ℂ) * ψ (c * z) := by
  have h1 : ∑ y : k, ψ (c * (y * y)) = ∑ z : k, ((quadraticChar k z : ℂ) + 1) * ψ (c * z) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun y : k => y ^ 2)]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h2 : ∀ y ∈ Finset.univ.filter (fun y : k => y ^ 2 = z), ψ (c * (y * y)) = ψ (c * z) := by
      intro y hy
      rw [← (Finset.mem_filter.1 hy).2, pow_two]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have h3 := quadraticChar_card_sqrts hchar z
    have h4 : ((Finset.univ.filter (fun y : k => y ^ 2 = z)).card : ℤ) = quadraticChar k z + 1 := by
      rw [← h3]
      congr 2
      ext y
      simp
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h4
  rw [h1]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib]
  have h5 : ∑ z : k, ψ (c * z) = 0 := by
    simp_rw [mul_comm c]
    rw [AddChar.sum_mulShift c (AddChar.IsPrimitive.of_ne_one hψ)]
    simp [hc]
  rw [h5, add_zero]

theorem sum_sq_scale (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c t : k}
    (hc : c ≠ 0) (ht : t ≠ 0) :
    ∑ y : k, ψ ((t * c) * (y * y)) = (quadraticChar k t : ℂ) * ∑ y : k, ψ (c * (y * y)) := by
  rw [sum_sq_eq hchar ψ hψ (mul_ne_zero ht hc), sum_sq_eq hchar ψ hψ hc, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft₀ t ht) _ _ fun z => ?_
  have h1 : (quadraticChar k t : ℂ) * (quadraticChar k t : ℂ) = 1 := by
    have := quadraticChar_sq_one ht
    have h2 : (quadraticChar k t) * (quadraticChar k t) = 1 := by rw [← pow_two]; exact this
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h2
  have e : (Equiv.mulLeft₀ t ht) z = t * z := rfl
  rw [e, map_mul (quadraticChar k) t z, Int.cast_mul, show t * c * z = c * (t * z) by ring]
  linear_combination (-(quadraticChar k z : ℂ) * ψ (c * (t * z))) * h1

end OneVar

section Form

variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_scale (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    {B : Matrix ι ι k} (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ}
    (hM : Fintype.card ι = 2 * M) {t : k} (ht : t ≠ 0) :
    ∑ x, ψ (t * quadForm B x) = ∑ x, ψ (quadForm B x) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  haveI : Invertible (2 : k) := invertibleOfNonzero h2
  let Q : QuadraticForm k (ι → k) := (2 : k)⁻¹ • Matrix.toQuadraticForm' B
  have hQ : ∀ x, Q x = quadForm B x := by
    intro x
    simp [Q, quadForm, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']
  have hsep : (QuadraticMap.associated (R := k) Q).SeparatingLeft := by
    intro x hx
    have hass : ∀ y, x ⬝ᵥ (B *ᵥ y) = 0 := by
      intro y
      have hxy : QuadraticMap.associatedHom k Q x y = 0 := hx y
      have hyx : QuadraticMap.associatedHom k Q y x = 0 := by
        rw [← QuadraticMap.associated_isSymm k Q x y]
        exact hxy
      have e1 := QuadraticMap.associated_eq_self_apply k Q (x + y)
      have e2 := QuadraticMap.associated_eq_self_apply k Q x
      have e3 := QuadraticMap.associated_eq_self_apply k Q y
      simp only [map_add, LinearMap.add_apply] at e1
      rw [hQ, quadForm_add h2 hB] at e1
      rw [hQ] at e2 e3
      linear_combination e2 + e3 - e1 + hxy + hyx
    have hz : B *ᵥ x = 0 := by
      funext i
      have h3 := hass (Pi.single i 1)
      have hs : x ⬝ᵥ (B *ᵥ (Pi.single i 1)) = (Pi.single i 1 : ι → k) ⬝ᵥ (B *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
      rw [hs, single_dotProduct, one_mul] at h3
      exact h3
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hz
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  have hsum : ∀ u : k, ∑ x, ψ (u * quadForm B x) = ∏ i, ∑ y : k, ψ ((u * (w i : k)) * (y * y)) := by
    intro u
    calc ∑ x, ψ (u * quadForm B x)
        = ∑ y : Fin (Module.finrank k (ι → k)) → k, ψ (u * ∑ i, (w i : k) * (y i * y i)) := by
          refine Fintype.sum_equiv e.toLinearEquiv.toEquiv _ _ fun x => ?_
          have h3 := e.map_app x
          rw [hQ, QuadraticMap.weightedSumSquares_apply] at h3
          simp only [Units.smul_def, smul_eq_mul] at h3
          rw [← h3]
          rfl
      _ = ∑ y : Fin (Module.finrank k (ι → k)) → k,
            ∏ i, ψ ((u * (w i : k)) * (y i * y i)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum, char_sum]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_assoc]
      _ = ∏ i, ∑ y : k, ψ ((u * (w i : k)) * (y * y)) := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have h1 := hsum 1
  simp only [one_mul] at h1
  rw [hsum t, h1]
  have hsc : ∀ i, ∑ y : k, ψ ((t * (w i : k)) * (y * y)) =
      (quadraticChar k t : ℂ) * ∑ y : k, ψ ((w i : k) * (y * y)) :=
    fun i => sum_sq_scale hchar ψ hψ (w i).ne_zero ht
  simp_rw [hsc]
  have hfr : Fintype.card (Fin (Module.finrank k (ι → k))) = 2 * M := by
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hM]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hfr, pow_mul]
  have h3 : (quadraticChar k t : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (quadraticChar_sq_one ht)
  rw [h3, one_pow, one_mul]

theorem card_quadric_unit (hchar : ringChar k ≠ 2) (M : ℕ) (hM : Fintype.card ι = 2 * M)
    (hM1 : 1 ≤ M) (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) {s : k} (hs : s ≠ 0) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ (M - 1) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  set G : ℂ := ∑ x, ψ (quadForm B x) with hG
  have hGn : ‖G‖ = (Fintype.card k : ℝ) ^ M := by
    have := norm_gauss ψ hψ1 h2 hB hdet hM (t := 1) one_ne_zero
    simpa [hG] using this
  have hrest : ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = -G := by
    have e1 : ∀ t ∈ Finset.univ.erase (0 : k),
        ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = ψ (t * (-s)) * G := by
      intro t ht
      rw [gauss_scale hchar ψ hψ1 hB hdet hM (Finset.ne_of_mem_erase ht), mul_neg]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_mul]
    have e2 : ∑ t : k, ψ (t * (-s)) = 0 := by
      rw [AddChar.sum_mulShift (-s) (AddChar.IsPrimitive.of_ne_one hψ1)]
      simp [hs]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at e2
    have e3 : ∑ t ∈ Finset.univ.erase (0 : k), ψ (t * (-s)) = -1 := by
      simp only [zero_mul, AddChar.map_zero_eq_one] at e2
      linear_combination e2
    rw [e3]
    ring
  rw [hrest] at hcount
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) = -G := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| =
      (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal, norm_neg, hGn]
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  have hpM : (Fintype.card k : ℝ) ^ M = (Fintype.card k : ℝ) ^ (M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hfac, abs_mul, abs_of_pos hq, hpM] at habs
  exact (mul_right_cancel₀ hq.ne' habs).le

end Form

end GlobalTheory.CompanionTheory.SW.QuadricUnit
