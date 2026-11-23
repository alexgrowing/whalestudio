import Mathlib

open Finset Matrix

namespace GlobalTheory

section Trace

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem exists_nat_trace_of_mul_self {E : Matrix A A ℂ} (hE : E * E = E) :
    ∃ r : ℕ, E.trace = r := by
  have h : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  exact ⟨_, by rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ h).trace]⟩

theorem exists_nat_trace_of_pow_four {V : Matrix A A ℂ} (hV : V ^ 4 = 1) :
    ∃ r : ℕ, (Fintype.card A : ℂ) + V.trace + (V ^ 2).trace + (V ^ 3).trace = 4 * r := by
  set S : Matrix A A ℂ := 1 + V + V ^ 2 + V ^ 3 with hS
  have h1 : V * S = S := by
    have : V * S = V + V ^ 2 + V ^ 3 + V ^ 4 := by rw [hS]; noncomm_ring
    rw [this, hV, hS]; abel
  have h2 : V ^ 2 * S = S := by rw [pow_two, mul_assoc, h1, h1]
  have h3 : V ^ 3 * S = S := by rw [pow_succ, mul_assoc, h1, h2]
  have h4 : S * S = (4 : ℂ) • S := by
    conv_lhs => rw [hS, add_mul, add_mul, add_mul, ← hS, one_mul, h1, h2, h3]
    module
  obtain ⟨r, hr⟩ := exists_nat_trace_of_mul_self (E := (4 : ℂ)⁻¹ • S) (by
    rw [smul_mul_smul_comm, h4, smul_smul]; norm_num)
  refine ⟨r, ?_⟩
  rw [← hr, hS]
  simp only [trace_smul, trace_add, trace_one, smul_eq_mul]
  ring

theorem trace_sq_of_pow_four {U : Matrix A A ℂ} (hU : U ^ 4 = 1) (h2 : (U ^ 2).trace = 1)
    (h13 : U.trace * (U ^ 3).trace = 1) (hodd : Odd (Fintype.card A)) :
    U.trace ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) := by
  obtain ⟨r, hr⟩ := exists_nat_trace_of_pow_four hU
  obtain ⟨t, ht⟩ := exists_nat_trace_of_pow_four (V := Complex.I • U) (by
    rw [smul_pow, hU, Complex.I_pow_four, one_smul])
  simp only [smul_pow, trace_smul, smul_eq_mul, h2, Complex.I_sq, Complex.I_pow_three] at hr ht
  set a := U.trace
  set b := (U ^ 3).trace
  set D := Fintype.card A
  have hm : a + b = ((4 * r - D - 1 : ℤ) : ℂ) := by push_cast; linear_combination hr
  have hn : Complex.I * (a - b) = ((4 * t - D + 1 : ℤ) : ℂ) := by push_cast; linear_combination ht
  have hmn : (4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 = 4 := by
    have : (((4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 : ℤ) : ℂ) = ((4 : ℤ) : ℂ) := by
      rw [Int.cast_add, Int.cast_pow, Int.cast_pow, ← hm, ← hn, mul_pow, Complex.I_sq]
      push_cast
      linear_combination 4 * h13
    exact_mod_cast this
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hodd) with h | h
  · have h0 : (4 * t - D + 1 : ℤ) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (4 * t - D + 1 : ℤ) = 4 * k := ⟨t - D / 4, by omega⟩
      rw [hk] at hmn ⊢
      have : k = 0 := by nlinarith [sq_nonneg (4 * r - D - 1 : ℤ), sq_nonneg k, sq_nonneg (k - 1), sq_nonneg (k+1), Int.one_le_abs (z := k), sq_abs k]
      simp [this]
    rw [h0] at hn
    have hab : a = b := by simpa [sub_eq_zero] using hn
    rw [ZMod.χ₄_nat_one_mod_four h, pow_two]
    simpa [← hab] using h13
  · have h0 : (4 * r - D - 1 : ℤ) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (4 * r - D - 1 : ℤ) = 4 * k := ⟨r - D / 4 - 1, by omega⟩
      rw [hk] at hmn ⊢
      have : k = 0 := by nlinarith [sq_nonneg (4 * t - D + 1 : ℤ), sq_nonneg k]
      simp [this]
    rw [h0] at hm
    rw [ZMod.χ₄_nat_three_mod_four h]
    push_cast at hm ⊢
    linear_combination a * hm - h13

end Trace

section Bicharacter

variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem eq_zero_of_add_self_eq_zero_of_odd_card (hodd : Odd (Fintype.card A)) {x : A}
    (hx : x + x = 0) : x = 0 := by
  obtain ⟨k, hk⟩ := hodd
  have h := card_nsmul_eq_zero (x := x)
  rwa [hk, add_nsmul, mul_comm, mul_nsmul', two_nsmul, hx, nsmul_zero, zero_add, one_nsmul] at h

theorem sq_sum_bicharacter (hodd : Odd (Fintype.card A)) (B : A → AddChar A ℂ)
    (hsymm : ∀ x y, B x y = B y x) (hnd : ∀ x, B x = 0 → x = 0) :
    (∑ x, B x x) ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) := by
  classical
  have hsum : ∀ x, ∑ y, B x y = if x = 0 then (Fintype.card A : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_eq_ite]
    refine if_congr ⟨hnd x, ?_⟩ rfl rfl
    rintro rfl
    ext y
    rw [hsymm]; simp
  have hD : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (Fintype.card A : ℂ) two_pos
  have hs0 : s ≠ 0 := by rintro rfl; exact hD (by simpa using hs.symm)
  let F : Matrix A A ℂ := Matrix.of fun x y => B x y
  let P : Matrix A A ℂ := Matrix.of fun x y => if x + y = 0 then 1 else 0
  have hFF : F * F = (Fintype.card A : ℂ) • P := by
    ext x z
    simp only [F, P, mul_apply, of_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← hsum]
    refine sum_congr rfl fun y _ => ?_
    rw [hsymm x y, hsymm (x + z) y, AddChar.map_add_eq_mul]
  have hPP : P * P = 1 := by
    ext x z
    simp only [P, mul_apply, of_apply, one_apply, add_eq_zero_iff_neg_eq, ite_mul, one_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true, neg_neg]
  have hP : P.trace = 1 := by
    have : ∀ x : A, x + x = 0 ↔ x = 0 := fun x =>
      ⟨eq_zero_of_add_self_eq_zero_of_odd_card hodd, fun h => by simp [h]⟩
    simp [P, trace, this]
  have hPF : (P * F).trace = ∑ x, B (-x) x := by
    simp [P, F, trace, mul_apply, add_eq_zero_iff_neg_eq]
  have hF : F.trace = ∑ x, B x x := by simp [F, trace]
  have hprod : F.trace * (P * F).trace = Fintype.card A := by
    rw [hF, hPF, sum_mul_sum, ← Fintype.sum_prod_type']
    let φ : A × A → A × A := fun p => (p.1 + p.2, p.1 - p.2)
    have hφ : Function.Bijective φ := by
      refine Finite.injective_iff_bijective.1 fun p q h => ?_
      have h1 : p.1 + p.2 = q.1 + q.2 := congrArg Prod.fst h
      have h2 : p.1 - p.2 = q.1 - q.2 := congrArg Prod.snd h
      have h3 : p.1 - q.1 = 0 := eq_zero_of_add_self_eq_zero_of_odd_card hodd (by
        have : p.1 - q.1 + (p.1 - q.1) =
            (p.1 + p.2 - (q.1 + q.2)) + (p.1 - p.2 - (q.1 - q.2)) := by abel
        rw [this, h1, h2]; simp)
      have h4 : p.1 = q.1 := sub_eq_zero.1 h3
      exact Prod.ext h4 (by rwa [h4, add_right_inj] at h1)
    rw [Fintype.sum_bijective φ hφ _ (fun p => B p.1 p.2), Fintype.sum_prod_type]
    · simp [hsum]
    · rintro ⟨x, y⟩
      simp only [φ]
      rw [hsymm (x + y), AddChar.map_add_eq_mul, hsymm (x - y) x, hsymm (x - y) y, sub_eq_add_neg,
        AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hsymm y x, hsymm (-y) y]
      have : B x (-y) * B x y = 1 := by rw [← AddChar.map_add_eq_mul]; simp
      linear_combination (-(B x x * B y (-y))) * this
  have hU2 : (s⁻¹ • F) ^ 2 = P := by
    rw [smul_pow, pow_two F, hFF, smul_smul, ← hs, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs0),
      one_smul]
  have key := trace_sq_of_pow_four (U := s⁻¹ • F)
    (by rw [show 4 = 2 + 2 from rfl, pow_add, hU2, hPP]) (by rw [hU2, hP])
    (by
      rw [pow_succ, hU2, mul_smul_comm, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
        mul_mul_mul_comm, hprod, ← hs]
      field_simp) hodd
  rw [← key, ← hs, trace_smul, hF, smul_eq_mul]
  field_simp

end Bicharacter

section Quadratic

variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem sq_sum_addChar_quadraticMap {M : Type*} [AddCommGroup M] (hodd : Odd (Fintype.card A))
    (q : QuadraticMap ℤ A M) (ψ : AddChar M ℂ)
    (hnd : ∀ x, (∀ y, ψ (QuadraticMap.polar q x y) = 1) → x = 0) :
    (∑ x, ψ (q x)) ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) := by
  let B : A → AddChar A ℂ := fun x => ψ.compAddMonoidHom (q.polarBilin (x + x)).toAddMonoidHom
  have hB : ∀ x y, B x y = ψ (QuadraticMap.polar q (x + x) y) := fun _ _ => rfl
  rw [← sq_sum_bicharacter hodd B]
  · congr 1
    have hφ : Function.Bijective fun x : A => x + x := by
      refine Finite.injective_iff_bijective.1 fun x y h => sub_eq_zero.1 ?_
      refine eq_zero_of_add_self_eq_zero_of_odd_card hodd ?_
      have h' : x + x = y + y := h
      rw [sub_add_sub_comm, h', sub_self]
    refine (Fintype.sum_bijective _ hφ _ _ fun x => ?_).symm
    rw [hB, QuadraticMap.polar_add_left, QuadraticMap.polar_self, QuadraticMap.map_add_self]
    congr 1
    module
  · intro x y
    rw [hB, hB, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left,
      QuadraticMap.polar_comm q x y]
  · intro x hx
    refine eq_zero_of_add_self_eq_zero_of_odd_card hodd (hnd _ fun y => ?_)
    rw [← hB, hx]; rfl

open Complex in
theorem periodic_exp_two_pi_rat :
    Function.Periodic (fun r : ℚ => exp (2 * Real.pi * I * r)) 1 := fun r => by
  simp only [Rat.cast_add, Rat.cast_one, mul_add, mul_one, exp_add, exp_two_pi_mul_I]

noncomputable def ratCircleChar : AddChar (AddCircle (1 : ℚ)) ℂ where
  toFun := periodic_exp_two_pi_rat.lift
  map_zero_eq_one' := by
    change Complex.exp _ = 1
    simp
  map_add_eq_mul' x y := by
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    change Complex.exp _ = Complex.exp _ * Complex.exp _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

@[simp]
theorem ratCircleChar_coe (r : ℚ) :
    ratCircleChar (r : AddCircle (1 : ℚ)) = Complex.exp (2 * Real.pi * Complex.I * r) := rfl

theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  induction x using QuotientAddGroup.induction_on with | H r => ?_
  rw [ratCircleChar_coe, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero] at hn
  refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
  rw [zsmul_eq_mul, mul_one]
  exact_mod_cast hn.symm

theorem sq_quadraticGaussSum (hodd : Odd (Fintype.card A))
    (q : QuadraticMap ℤ A (AddCircle (1 : ℚ)))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar q x y = 0) → x = 0) :
    (∑ x, ratCircleChar (q x)) ^ 2 =
      (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) :=
  sq_sum_addChar_quadraticMap hodd q _ fun x hx =>
    hnd x fun y => ratCircleChar_eq_one_iff.1 (hx y)

end Quadratic

section Matrices

variable {n : Type*} [Fintype n]

noncomputable def halfQuadraticModOne (M : Matrix n n ℚ) :
    QuadraticMap ℤ (n → ℤ) (AddCircle (1 : ℚ)) :=
  LinearMap.BilinMap.toQuadraticMap <| LinearMap.mk₂ ℤ
    (fun x y : n → ℤ =>
      ((((fun i => (x i : ℚ)) ⬝ᵥ M *ᵥ fun i => (y i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)))
    (fun x x' y => by
      rw [← AddCircle.coe_add, ← add_div, ← add_dotProduct]
      congr 3; ext; simp)
    (fun c x y => by
      rw [← AddCircle.coe_zsmul, ← smul_div_assoc, ← smul_dotProduct]
      congr 3; ext; simp)
    (fun x y y' => by
      rw [← AddCircle.coe_add, ← add_div, ← dotProduct_add, ← mulVec_add]
      congr 4; ext; simp)
    (fun c x y => by
      rw [← AddCircle.coe_zsmul, ← smul_div_assoc, ← dotProduct_smul, ← mulVec_smul]
      congr 4; ext; simp)

theorem halfQuadraticModOne_apply (M : Matrix n n ℚ) (x : n → ℤ) :
    halfQuadraticModOne M x =
      ((((fun i => (x i : ℚ)) ⬝ᵥ M *ᵥ fun i => (x i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)) := rfl

theorem polar_halfQuadraticModOne {M : Matrix n n ℚ} (hM : M.IsSymm) (x y : n → ℤ) :
    QuadraticMap.polar (halfQuadraticModOne M) x y =
      (((fun i => (y i : ℚ)) ⬝ᵥ M *ᵥ (fun i => (x i : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [halfQuadraticModOne, LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.mk₂_apply,
    LinearMap.mk₂_apply, ← AddCircle.coe_add, dotProduct_mulVec, ← mulVec_transpose, hM.eq,
    dotProduct_comm, add_halves]

variable [DecidableEq n] {b d : Matrix n n ℤ}

theorem isUnit_det_map_ratCast (hd : d.det ≠ 0) : IsUnit (d.map ((↑) : ℤ → ℚ)).det := by
  rw [← Int.cast_det]; simpa using hd

theorem isSymm_mul_inv_of_isSymm (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm) :
    (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹).IsSymm := by
  have hu := isUnit_det_map_ratCast hd
  have hs' := (hs.map (Int.castRingHom ℚ)).eq
  rw [Matrix.map_mul, transpose_map, transpose_mul, transpose_transpose] at hs'
  simp only [Int.coe_castRingHom] at hs'
  rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv]
  set B := b.map ((↑) : ℤ → ℚ)
  set D := d.map ((↑) : ℤ → ℚ)
  calc Dᵀ⁻¹ * Bᵀ = Dᵀ⁻¹ * (Bᵀ * D) * D⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = B * D⁻¹ := by
        rw [hs', ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_transpose _ hu), Matrix.one_mul]

omit [DecidableEq n] in
theorem intCast_mulVec (d : Matrix n n ℤ) (x : n → ℤ) :
    (fun i => ((d *ᵥ x) i : ℚ)) = d.map ((↑) : ℤ → ℚ) *ᵥ fun i => (x i : ℚ) := by
  ext i; simp [mulVec, dotProduct]

omit [DecidableEq n] in
theorem intCast_dotProduct (x y : n → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℚ) = (fun i => (x i : ℚ)) ⬝ᵥ fun i => (y i : ℚ) := by
  simp [dotProduct]

theorem range_le_radical_halfQuadraticModOne (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) :
    LinearMap.range d.mulVecLin ≤
      (halfQuadraticModOne (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹)).radical := by
  rintro _ ⟨μ, rfl⟩
  have hu := isUnit_det_map_ratCast hd
  have key : (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ (fun i => ((d *ᵥ μ) i : ℚ)) =
      fun i => ((b *ᵥ μ) i : ℚ) := by
    rw [intCast_mulVec, intCast_mulVec, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu,
      Matrix.mul_one]
  refine ⟨?_, LinearMap.ext fun y => ?_⟩
  · obtain ⟨k, hk⟩ := he μ
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at hk
    rw [mulVecLin_apply, halfQuadraticModOne_apply, key, ← intCast_dotProduct, hk]
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨k, by simp⟩
  · rw [QuadraticMap.polarBilin_apply_apply,
      polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), mulVecLin_apply, key,
      ← intCast_dotProduct]
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨_, by rw [zsmul_eq_mul, mul_one]⟩

noncomputable def pairQuadraticForm (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) :
    QuadraticMap ℤ ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) (AddCircle (1 : ℚ)) :=
  QuadraticMap.lift _ _ (range_le_radical_halfQuadraticModOne hd hs he)

theorem pairQuadraticForm_mk (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    pairQuadraticForm hd hs he (Submodule.Quotient.mk ν) =
      ((((fun i => (ν i : ℚ)) ⬝ᵥ (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ
        fun i => (ν i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)) := rfl

theorem ratCircleChar_pairQuadraticForm_mk (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    ratCircleChar (pairQuadraticForm hd hs he (Submodule.Quotient.mk ν)) =
      Complex.exp (Real.pi * Complex.I *
        ((fun i => (ν i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (ν i : ℂ))) := by
  have hinv : (d.map ((↑) : ℤ → ℂ))⁻¹ = (d.map ((↑) : ℤ → ℚ))⁻¹.map (Rat.castHom ℂ) := by
    refine inv_eq_right_inv ?_
    have : d.map ((↑) : ℤ → ℂ) = (d.map ((↑) : ℤ → ℚ)).map (Rat.castHom ℂ) := by ext; simp
    rw [this, ← Matrix.map_mul, mul_nonsing_inv _ (isUnit_det_map_ratCast hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [pairQuadraticForm_mk, ratCircleChar_coe, hinv]
  congr 1
  simp only [dotProduct, mulVec, mul_apply, map_apply, Rat.coe_castHom]
  push_cast
  ring

theorem pairQuadraticForm_nondegenerate (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    (x : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)
    (hx : ∀ y, QuadraticMap.polar (pairQuadraticForm hd hs he) x y = 0) : x = 0 := by
  obtain ⟨ν, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨u, v, huv⟩ := hc
  have hu := isUnit_det_map_ratCast hd
  have hint : ∀ i, ∃ k : ℤ, (k : ℚ) = ((b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ
      fun i => (ν i : ℚ)) i := by
    intro i
    have h : QuadraticMap.polar
        (halfQuadraticModOne (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹)) ν (Pi.single i 1) = 0 :=
      hx (Submodule.Quotient.mk (Pi.single i 1))
    rw [polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), AddCircle.coe_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    simpa [dotProduct, Pi.single_apply] using hk
  choose w hw using hint
  have huv' : u.map ((↑) : ℤ → ℚ) * b.map (↑) + v.map (↑) * d.map (↑) = 1 := by
    have := congrArg (Int.castRingHom ℚ).mapMatrix huv
    rwa [map_add, map_mul, map_mul, map_one] at this
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨u *ᵥ w + v *ᵥ ν, ?_⟩
  have h1 : (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) =
      (d.map ((↑) : ℤ → ℚ))⁻¹ *ᵥ fun i => (ν i : ℚ) := by
    have : (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) =
        (fun i => ((u *ᵥ w) i : ℚ)) + fun i => ((v *ᵥ ν) i : ℚ) := by ext; simp
    rw [this, intCast_mulVec, intCast_mulVec, funext hw, mulVec_mulVec, ← add_mulVec]
    congr 1
    conv_rhs => rw [← Matrix.one_mul (d.map ((↑) : ℤ → ℚ))⁻¹, ← huv', Matrix.add_mul,
      Matrix.mul_assoc _ (d.map _), mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.mul_assoc]
  have h2 := intCast_mulVec d (u *ᵥ w + v *ᵥ ν)
  rw [h1, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec] at h2
  ext i
  exact_mod_cast congrFun h2 i

theorem natCard_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    Nat.card ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) = d.det.natAbs := by
  have hinj : Function.Injective d.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    exact fun v hv => eq_zero_of_mulVec_eq_zero hd hv
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← LinearMap.det_toLin']
  rfl

theorem finite_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    Finite ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_quotient_range_mulVecLin hd]; simpa using hd)

theorem chi_four_natAbs_mul (D : ℤ) :
    ZMod.χ₄ (D.natAbs : ZMod 4) * D.natAbs = ZMod.χ₄ (D : ZMod 4) * D := by
  obtain ⟨m, rfl | rfl⟩ := D.eq_nat_or_neg
  · simp
  · have : ∀ a : ZMod 4, ZMod.χ₄ (-a) = -ZMod.χ₄ a := by decide
    simp [this]

theorem sq_sum_pairQuadraticForm (hodd : Odd d.det) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    [Fintype ((n → ℤ) ⧸ LinearMap.range d.mulVecLin)] :
    (∑ x, ratCircleChar (pairQuadraticForm (by rintro h; simp [h] at hodd) hs he x)) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by
  have hd : d.det ≠ 0 := by rintro h; simp [h] at hodd
  have hcard := natCard_quotient_range_mulVecLin hd
  rw [Nat.card_eq_fintype_card] at hcard
  rw [sq_quadraticGaussSum (by rw [hcard]; exact hodd.natAbs) _
    (pairQuadraticForm_nondegenerate hd hs he hc), hcard]
  rw [← Int.cast_natCast (R := ℂ), ← Int.cast_mul, chi_four_natAbs_mul, Int.cast_mul]

omit [DecidableEq n] in

theorem even_dotProduct_mulVec_of_two_dvd (hb : ∀ i j, 2 ∣ b i j) (d : Matrix n n ℤ) (μ : n → ℤ) :
    Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ) := by
  rw [even_iff_two_dvd]
  simp only [dotProduct, mulVec, mul_apply]
  exact dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_sum fun j _ => Dvd.dvd.mul_right
    (dvd_sum fun k _ => (hb k j).mul_left _) _) _

theorem sq_sum_exp_pair (hodd : Odd d.det) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    {ι : Type*} [Fintype ι] (r : ι → n → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)) :
    (∑ k, Complex.exp (Real.pi * Complex.I *
        ((fun i => (r k i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (r k i : ℂ)))) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by
  letI := Fintype.ofBijective _ hr
  rw [← sq_sum_pairQuadraticForm hodd hs he hc]
  congr 1
  exact Fintype.sum_bijective _ hr _ _ fun k => (ratCircleChar_pairQuadraticForm_mk _ hs he _).symm

theorem symm_coprime_of_mem_symplecticGroup {a c : Matrix n n ℤ}
    (h : fromBlocks a b c d ∈ symplecticGroup n ℤ) :
    (dᵀ * b).IsSymm ∧ ∃ u v : Matrix n n ℤ, u * b + v * d = 1 := by
  rw [SymplecticGroup.mem_iff', J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  obtain ⟨-, h1, -, h2⟩ := h
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2
  refine ⟨?_, -cᵀ, aᵀ, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_transpose]
    exact (add_neg_eq_zero.1 h2).symm
  · rw [← neg_inj, ← h1, Matrix.neg_mul, neg_add, neg_neg]

theorem exists_representatives_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    ∃ r : Fin d.det.natAbs → n → ℤ, Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin) := by
  haveI := finite_quotient_range_mulVecLin hd
  let e := (Finite.equivFinOfCardEq (natCard_quotient_range_mulVecLin hd)).symm
  refine ⟨fun k => (e k).out, ?_⟩
  convert e.bijective using 2
  exact Submodule.Quotient.mk_out _

end Matrices

end GlobalTheory
