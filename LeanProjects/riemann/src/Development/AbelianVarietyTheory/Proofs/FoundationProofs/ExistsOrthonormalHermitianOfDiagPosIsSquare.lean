import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt

open NumberField
open scoped Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.SqDet

section
variable {K : Type} [Field K] [NumberField K] {d : ℕ} {θ : K}

end

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem exists_rat_sum_norm_forms_eq_one {a b d : ℚ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ∃ p₁ q₁ p₂ q₂ : ℚ, a * (p₁ ^ 2 + d * q₁ ^ 2) + b * (p₂ ^ 2 + d * q₂ ^ 2) = 1 := by
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt ℚ
    (![a, a * d, b, b * d, -1] : Fin 5 → ℚ) (by simp)
    (by
      intro i
      fin_cases i <;> simp [ha.ne', hb.ne', hd.ne'])
    (by
      intro τ
      refine ⟨4, 0, ?_, ?_⟩
      · simp
      · simp only [Matrix.cons_val_zero, eq_ratCast]
        exact_mod_cast ha)
  have hx' : a * x 0 ^ 2 + a * d * x 1 ^ 2 + b * x 2 ^ 2 + b * d * x 3 ^ 2 = x 4 ^ 2 := by
    simp [Fin.sum_univ_five] at hx
    linarith
  have t0 : 0 ≤ a * x 0 ^ 2 := by positivity
  have t1 : 0 ≤ a * d * x 1 ^ 2 := by positivity
  have t2 : 0 ≤ b * x 2 ^ 2 := by positivity
  have t3 : 0 ≤ b * d * x 3 ^ 2 := by positivity
  have h4 : x 4 ≠ 0 := by
    intro h4
    rw [h4] at hx'
    have e0 : a * x 0 ^ 2 = 0 := by linarith
    have e1 : a * d * x 1 ^ 2 = 0 := by linarith
    have e2 : b * x 2 ^ 2 = 0 := by linarith
    have e3 : b * d * x 3 ^ 2 = 0 := by linarith
    apply hx0
    funext i
    fin_cases i
    · simpa [ha.ne'] using e0
    · simpa [ha.ne', hd.ne'] using e1
    · simpa [hb.ne'] using e2
    · simpa [hb.ne', hd.ne'] using e3
    · exact h4
  refine ⟨x 0 / x 4, x 1 / x 4, x 2 / x 4, x 3 / x 4, ?_⟩
  field_simp
  linarith

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem sesq_apply_eq_zero_and_of_mem_span_of_forall_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {σ : K →+* K} (h : V →ₗ[K] V →ₛₗ[σ] K) {s : Set V} {w : V}
    (hs : ∀ u ∈ s, h u w = 0 ∧ h w u = 0) {u : V} (hu : u ∈ Submodule.span K s) :
    h u w = 0 ∧ h w u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx.1, hy.1, hx.2, hy.2]
  | smul c x _ hx => simp [hx.1, hx.2]

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem exists_orthonormal_mem_span_of_diagonal_square_prod {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) {d : ℕ} {θ : K}
    (hd : 0 < d) (hθ2 : θ ^ 2 = -(d : K)) (hθ : σ θ = -θ) :
    ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) →
      (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) →
      ∃ e : Fin r → V, (∀ i j, h (e i) (e j) = if i = j then 1 else 0) ∧
        ∀ i, e i ∈ Submodule.span K (Set.range v) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro v a ha hv hsq
  rcases r with _ | _ | r
  · exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · obtain ⟨s, hs⟩ := hsq
    rw [Fin.prod_univ_one] at hs
    have hs0 : (s : K) ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        have := ha 0
        rw [hs] at this
        simp at this
      exact_mod_cast this
    refine ⟨fun _ => ((s⁻¹ : ℚ) : K) • v 0, ?_, fun _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨0, rfl⟩)⟩
    intro i j
    have hij : i = j := Fin.ext (by have := i.2; have := j.2; omega)
    subst hij
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hv, if_true, map_ratCast,
      hs]
    push_cast
    field_simp
  · have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    obtain ⟨p₁, q₁, p₂, q₂, hq⟩ := exists_rat_sum_norm_forms_eq_one (ha 0) (ha 1) hdq
    have hqK : (a 0 : K) * ((p₁ : K) ^ 2 + (d : K) * (q₁ : K) ^ 2) +
        (a 1 : K) * ((p₂ : K) ^ 2 + (d : K) * (q₂ : K) ^ 2) = 1 := by
      exact_mod_cast hq
    have h01 : (0 : Fin (r + 2)) ≠ 1 := by simp
    have hss : ∀ i : Fin r, (i.succ.succ : Fin (r + 2)) ≠ 0 ∧ (i.succ.succ : Fin (r + 2)) ≠ 1 := by
      intro i
      refine ⟨Fin.succ_ne_zero _, ?_⟩
      rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
      exact Fin.succ_ne_zero _
    have hv00 := hv 0 0
    have hv11 := hv 1 1
    have hv01 := hv 0 1
    have hv10 := hv 1 0
    simp only [if_true, h01, h01.symm, if_false] at hv00 hv11 hv01 hv10
    have hvs : ∀ (i : Fin r) (j : Fin (r + 2)), j = 0 ∨ j = 1 →
        h (v i.succ.succ) (v j) = 0 ∧ h (v j) (v i.succ.succ) = 0 := by
      intro i j hj
      rw [hv, hv]
      rcases hj with rfl | rfl
      · simp [(hss i).1, (hss i).1.symm]
      · simp [(hss i).2, (hss i).2.symm]
    set w : V := ((p₁ : K) + (q₁ : K) * θ) • v 0 + ((p₂ : K) + (q₂ : K) * θ) • v 1 with hw
    set w' : V := ((a 1 : K) * ((p₂ : K) - (q₂ : K) * θ)) • v 0 -
      ((a 0 : K) * ((p₁ : K) - (q₁ : K) * θ)) • v 1 with hw'
    have hww : h w w = 1 := by
      simp only [hw, map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hv00, hv11, hv01, hv10, map_mul, map_ratCast, hθ]
      linear_combination hqK - ((a 0 : K) * (q₁ : K) ^ 2 + (a 1 : K) * (q₂ : K) ^ 2) * hθ2
    have hww' : h w w' = 0 := by
      simp only [hw, hw', map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv00, hv11, hv01, hv10, map_mul,
        map_ratCast, hθ]
      ring
    have hw'w : h w' w = 0 := by
      simp only [hw, hw', map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv00, hv11, hv01, hv10, map_mul,
        map_ratCast, hθ]
      ring
    have hw'w' : h w' w' = ((a 0 * a 1 : ℚ) : K) := by
      simp only [hw', map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hv00, hv11, hv01, hv10, map_mul, map_ratCast, hθ, map_neg]
      push_cast
      linear_combination (a 0 : K) * (a 1 : K) * hqK -
        (a 0 : K) * (a 1 : K) * ((a 0 : K) * (q₁ : K) ^ 2 + (a 1 : K) * (q₂ : K) ^ 2) * hθ2
    have hwv : ∀ i : Fin r, h (v i.succ.succ) w = 0 ∧ h w (v i.succ.succ) = 0 := by
      intro i
      obtain ⟨h1, h1'⟩ := hvs i 0 (Or.inl rfl)
      obtain ⟨h2, h2'⟩ := hvs i 1 (Or.inr rfl)
      constructor
      · simp [hw, h1, h2]
      · simp [hw, h1', h2']
    have hw'v : ∀ i : Fin r, h (v i.succ.succ) w' = 0 ∧ h w' (v i.succ.succ) = 0 := by
      intro i
      obtain ⟨h1, h1'⟩ := hvs i 0 (Or.inl rfl)
      obtain ⟨h2, h2'⟩ := hvs i 1 (Or.inr rfl)
      constructor
      · simp [hw', h1, h2]
      · simp [hw', h1', h2']
    have hwspan : w ∈ Submodule.span K (Set.range v) :=
      add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    have hw'span : w' ∈ Submodule.span K (Set.range v) :=
      sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    let v' : Fin (r + 1) → V := Fin.cons w' (fun i => v i.succ.succ)
    let a' : Fin (r + 1) → ℚ := Fin.cons (a 0 * a 1) (fun i => a i.succ.succ)
    have ha' : ∀ i, 0 < a' i := by
      intro i
      cases i using Fin.cases with
      | zero => exact mul_pos (ha 0) (ha 1)
      | succ i => exact ha _
    have hv' : ∀ i j, h (v' i) (v' j) = if i = j then (a' i : K) else 0 := by
      intro i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simpa [v', a'] using hw'w'
        | succ j => simpa [v', a', (Fin.succ_ne_zero j).symm] using (hw'v j).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa [v', a', Fin.succ_ne_zero i] using (hw'v i).1
        | succ j =>
          simp only [v', a', Fin.cons_succ, hv, Fin.succ_inj]
    have hsq' : IsSquare (∏ i, a' i) := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at hsq
      rw [Fin.prod_univ_succ]
      simp only [a', Fin.cons_zero, Fin.cons_succ]
      convert hsq using 1
      simp only [Fin.succ_zero_eq_one]
      ring
    obtain ⟨e', he', hspan'⟩ := ih (r + 1) (by omega) v' a' ha' hv' hsq'
    have hwe' : ∀ j, h (e' j) w = 0 ∧ h w (e' j) = 0 := by
      intro j
      refine sesq_apply_eq_zero_and_of_mem_span_of_forall_mem h ?_ (hspan' j)
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact ⟨by simpa [v'] using hw'w, by simpa [v'] using hww'⟩
      | succ i => simpa [v'] using hwv i
    have hle : Submodule.span K (Set.range v') ≤ Submodule.span K (Set.range v) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => simpa [v'] using hw'span
      | succ i => exact Submodule.subset_span ⟨i.succ.succ, rfl⟩
    refine ⟨Fin.cons w e', ?_, ?_⟩
    · intro i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simpa using hww
        | succ j => simpa [(Fin.succ_ne_zero j).symm] using (hwe' j).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa [Fin.succ_ne_zero i] using (hwe' i).1
        | succ j => simpa [Fin.succ_inj] using he' i j
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hwspan
      | succ i => simpa using hle (hspan' i)

open NumberField in
open scoped Matrix ComplexConjugate in

theorem _root_.GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare :
    ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (d : ℕ) (θ : K), 0 < d → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) → (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) → ∃ e : Fin r → V, ∀ i j, h (e i) (e j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ σ h d θ hd hθ2 hθ _ r v a ha hv hsq
  obtain ⟨e, he, -⟩ := exists_orthonormal_mem_span_of_diagonal_square_prod σ h hd hθ2 hθ r v a ha hv hsq
  exact ⟨e, he⟩

end GlobalTheory.SqDet
