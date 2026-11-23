import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoIntSmulOfFixesJK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponents

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.Scal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma sl_ofSL_sl_jK_eq_of_mul_eq_ofSL_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : _root_.GlobalTheory.KZ.Tower Ω ε) (G : _root_.GlobalTheory.KZ.GQ) (γ γ' : SL(2, ℤ))
    (h : ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      ((_root_.GlobalTheory.KZ.ofSL γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((_root_.GlobalTheory.KZ.ofSL γ' : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) :
    X.sl (_root_.GlobalTheory.KZ.ofSL γ)
      (X.sl G X.jK) = X.sl G X.jK := by
  have hG : G * _root_.GlobalTheory.KZ.ofSL γ = _root_.GlobalTheory.KZ.ofSL γ' * G := Subtype.ext (Units.ext h)
  rw [← _root_.GlobalTheory.KZ.Tower.sl_mul, hG,
    _root_.GlobalTheory.KZ.Tower.sl_mul,
    _root_.GlobalTheory.KZ.Tower.j_inv]

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma sl_ofSL_sl_jK_eq_of_mul_eq_intMatrix_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : _root_.GlobalTheory.KZ.Tower Ω ε) (G : _root_.GlobalTheory.KZ.GQ) (γ : SL(2, ℤ))
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 1)
    (h : ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      ((_root_.GlobalTheory.KZ.ofSL γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      M.map (Int.cast : ℤ → ℚ) * ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) :
    X.sl (_root_.GlobalTheory.KZ.ofSL γ)
      (X.sl G X.jK) = X.sl G X.jK := by
  refine sl_ofSL_sl_jK_eq_of_mul_eq_ofSL_mul X G γ ⟨M, hM⟩ ?_
  rw [h]
  congr 1

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma ofSL_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((_root_.GlobalTheory.KZ.ofSL γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
  simp [_root_.GlobalTheory.KZ.ofSL]

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma toGQ_apply (M : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < M.det)
    (i j : Fin 2) :
    ((_root_.GlobalTheory.KZ.toGQ M : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = (M i j : ℚ) := by
  simp [_root_.GlobalTheory.KZ.toGQ, h]

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma exists_ofSL_mul_upperTriangular (A : _root_.GlobalTheory.KZ.GQ) :
    ∃ (σ : SL(2, ℤ)) (T : _root_.GlobalTheory.KZ.GQ), _root_.GlobalTheory.KZ.ent T 1 0 = 0 ∧
      A = _root_.GlobalTheory.KZ.ofSL σ * T := by
  have hdet := A.2
  change 0 < Matrix.det ((A : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) at hdet
  rw [Matrix.det_fin_two] at hdet
  change 0 < _root_.GlobalTheory.KZ.ent A 0 0 * _root_.GlobalTheory.KZ.ent A 1 1 -
    _root_.GlobalTheory.KZ.ent A 0 1 * _root_.GlobalTheory.KZ.ent A 1 0 at hdet
  set p := _root_.GlobalTheory.KZ.ent A 0 0 with hp
  set q := _root_.GlobalTheory.KZ.ent A 1 0 with hq
  set x₀ : ℤ := q.num * p.den with hx₀
  set y₀ : ℤ := -(p.num * q.den) with hy₀
  have hne : x₀ ≠ 0 ∨ y₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hp0 : p = 0 := by
      have : p.num * q.den = 0 := by simpa [hy₀] using hcon.2
      rcases mul_eq_zero.1 this with h | h
      · exact Rat.num_eq_zero.1 h
      · exact absurd h (by exact_mod_cast q.den_nz)
    have hq0 : q = 0 := by
      have : q.num * p.den = 0 := by simpa [hx₀] using hcon.1
      rcases mul_eq_zero.1 this with h | h
      · exact Rat.num_eq_zero.1 h
      · exact absurd h (by exact_mod_cast p.den_nz)
    rw [hp0, hq0] at hdet
    simp at hdet
  have hg : 0 < Int.gcd x₀ y₀ := Int.gcd_pos_iff.2 hne
  have hcop : IsCoprime (x₀ / Int.gcd x₀ y₀) (y₀ / Int.gcd x₀ y₀) :=
    Int.isCoprime_iff_gcd_eq_one.2 (Int.gcd_div_gcd_div_gcd hg)
  obtain ⟨τ, -, hτ⟩ := ModularGroup.bottom_row_surj (R := ℤ)
    (show ![x₀ / Int.gcd x₀ y₀, y₀ / Int.gcd x₀ y₀] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from hcop)
  have hτ0 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = x₀ / Int.gcd x₀ y₀ := congrFun hτ 0
  have hτ1 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = y₀ / Int.gcd x₀ y₀ := congrFun hτ 1
  refine ⟨τ⁻¹, _root_.GlobalTheory.KZ.ofSL τ * A, ?_, by rw [map_inv, inv_mul_cancel_left]⟩
  have hx : (x₀ : ℚ) = ((x₀ / Int.gcd x₀ y₀ : ℤ) : ℚ) * (Int.gcd x₀ y₀ : ℤ) := by
    exact_mod_cast (Int.ediv_mul_cancel (Int.gcd_dvd_left x₀ y₀)).symm
  have hy : (y₀ : ℚ) = ((y₀ / Int.gcd x₀ y₀ : ℤ) : ℚ) * (Int.gcd x₀ y₀ : ℤ) := by
    exact_mod_cast (Int.ediv_mul_cancel (Int.gcd_dvd_right x₀ y₀)).symm
  have hzero : (x₀ : ℚ) * p + y₀ * q = 0 := by
    have h1 : (p.den : ℚ) * p = p.num := by exact_mod_cast Rat.den_mul_eq_num p
    have h2 : (q.den : ℚ) * q = q.num := by exact_mod_cast Rat.den_mul_eq_num q
    rw [hx₀, hy₀]
    push_cast
    linear_combination (q.num : ℚ) * h1 - (p.num : ℚ) * h2
  have hgq : ((Int.gcd x₀ y₀ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hentry : _root_.GlobalTheory.KZ.ent (_root_.GlobalTheory.KZ.ofSL τ * A) 1 0 =
      ((τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) * p + ((τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℚ) * q := by
    simp [_root_.GlobalTheory.KZ.ent, _root_.GlobalTheory.KZ.ofSL, Matrix.mul_apply, Fin.sum_univ_two, hp, hq]
  rw [hentry, hτ0, hτ1]
  apply mul_right_cancel₀ hgq
  rw [zero_mul, ← hzero, hx, hy]
  ring

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma diag_ne_zero_and_ratio_pos_of_upperTriangular (S : _root_.GlobalTheory.KZ.GQ) (hS : _root_.GlobalTheory.KZ.ent S 1 0 = 0) :
    _root_.GlobalTheory.KZ.ent S 1 1 ≠ 0 ∧ _root_.GlobalTheory.KZ.ent S 0 0 ≠ 0 ∧
      0 < _root_.GlobalTheory.KZ.ent S 0 0 / _root_.GlobalTheory.KZ.ent S 1 1 := by
  have h := S.2
  change 0 < Matrix.det ((S : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) at h
  rw [Matrix.det_fin_two] at h
  change 0 < _root_.GlobalTheory.KZ.ent S 0 0 * _root_.GlobalTheory.KZ.ent S 1 1 -
    _root_.GlobalTheory.KZ.ent S 0 1 * _root_.GlobalTheory.KZ.ent S 1 0 at h
  rw [hS, mul_zero, sub_zero] at h
  have hd : _root_.GlobalTheory.KZ.ent S 1 1 ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
  have ha : _root_.GlobalTheory.KZ.ent S 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
  refine ⟨hd, ha, ?_⟩
  have : _root_.GlobalTheory.KZ.ent S 0 0 / _root_.GlobalTheory.KZ.ent S 1 1 =
      _root_.GlobalTheory.KZ.ent S 0 0 * _root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 1 1 ^ 2 := by
    field_simp
  rw [this]
  exact div_pos h (by positivity)

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma exp_sl_jK_coeff_lowest_of_upperTriangular {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (S : _root_.GlobalTheory.KZ.GQ)
    (hS : _root_.GlobalTheory.KZ.ent S 1 0 = 0) :
    (X.exp (X.sl S X.jK)).coeff (-(_root_.GlobalTheory.KZ.ent S 0 0 / _root_.GlobalTheory.KZ.ent S 1 1)) =
      _root_.GlobalTheory.KZ.eOm ε (-(_root_.GlobalTheory.KZ.ent S 0 1 / _root_.GlobalTheory.KZ.ent S 1 1)) ∧
    ∀ s < -(_root_.GlobalTheory.KZ.ent S 0 0 / _root_.GlobalTheory.KZ.ent S 1 1), (X.exp (X.sl S X.jK)).coeff s = 0 := by
  obtain ⟨hd, ha, hpos⟩ := diag_ne_zero_and_ratio_pos_of_upperTriangular S hS
  obtain ⟨h1, hlow, -⟩ := X.j_exp
  constructor
  · have h := X.exp_upper S hS X.jK (-1)
    rw [h1, mul_one] at h
    convert h using 2 <;> ring
  · intro s hs
    have h := X.exp_upper S hS X.jK
      (s * _root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 0 0)
    have hr : s * _root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 0 0 < -1 := by
      have hinv : 0 < _root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 0 0 := by
        have := inv_pos.2 hpos; rwa [inv_div] at this
      calc s * _root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 0 0
          = s * (_root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 0 0) := by ring
        _ < -(_root_.GlobalTheory.KZ.ent S 0 0 / _root_.GlobalTheory.KZ.ent S 1 1) *
            (_root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 0 0) := mul_lt_mul_of_pos_right hs hinv
        _ = -1 := by
          rw [neg_mul, div_mul_div_comm, mul_comm (_root_.GlobalTheory.KZ.ent S 0 0),
            div_self (mul_ne_zero hd ha)]
    rw [hlow _ hr, mul_zero] at h
    have hs' : s * _root_.GlobalTheory.KZ.ent S 1 1 / _root_.GlobalTheory.KZ.ent S 0 0 * _root_.GlobalTheory.KZ.ent S 0 0 /
        _root_.GlobalTheory.KZ.ent S 1 1 = s := by field_simp
    rwa [hs'] at h

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma entry_ratios_eq_of_upperTriangular_sl_jK_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (S T : _root_.GlobalTheory.KZ.GQ)
    (hS : _root_.GlobalTheory.KZ.ent S 1 0 = 0) (hT : _root_.GlobalTheory.KZ.ent T 1 0 = 0)
    (h : X.sl S X.jK = X.sl T X.jK) :
    _root_.GlobalTheory.KZ.ent S 0 0 / _root_.GlobalTheory.KZ.ent S 1 1 = _root_.GlobalTheory.KZ.ent T 0 0 / _root_.GlobalTheory.KZ.ent T 1 1 ∧
      ∃ k : ℤ, _root_.GlobalTheory.KZ.ent S 0 1 / _root_.GlobalTheory.KZ.ent S 1 1 =
        _root_.GlobalTheory.KZ.ent T 0 1 / _root_.GlobalTheory.KZ.ent T 1 1 + k := by
  obtain ⟨hSl, hSz⟩ := exp_sl_jK_coeff_lowest_of_upperTriangular X S hS
  obtain ⟨hTl, hTz⟩ := exp_sl_jK_coeff_lowest_of_upperTriangular X T hT
  rw [h] at hSl hSz
  have hρ : _root_.GlobalTheory.KZ.ent S 0 0 / _root_.GlobalTheory.KZ.ent S 1 1 =
      _root_.GlobalTheory.KZ.ent T 0 0 / _root_.GlobalTheory.KZ.ent T 1 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact _root_.GlobalTheory.KZ.ES.JStab.eOm_ne_zero' ε _ (hTl.symm.trans (hSz _ (neg_lt_neg hlt)))
    · exact _root_.GlobalTheory.KZ.ES.JStab.eOm_ne_zero' ε _ (hSl.symm.trans (hTz _ (neg_lt_neg hlt)))
  refine ⟨hρ, ?_⟩
  rw [hρ] at hSl
  have he := congrArg ε (hSl.symm.trans hTl)
  rw [_root_.GlobalTheory.Glue.KTExp.map_eOm, _root_.GlobalTheory.Glue.KTExp.map_eOm, Complex.exp_eq_exp_iff_exists_int] at he
  obtain ⟨n, hn⟩ := he
  refine ⟨-n, ?_⟩
  have key : ((_root_.GlobalTheory.KZ.ent S 0 1 / _root_.GlobalTheory.KZ.ent S 1 1 : ℚ) : ℂ) =
      ((_root_.GlobalTheory.KZ.ent T 0 1 / _root_.GlobalTheory.KZ.ent T 1 1 + ((-n : ℤ) : ℚ) : ℚ) : ℂ) := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2
    push_cast at hn ⊢
    linear_combination -hn
  exact_mod_cast key

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma exists_smul_ofSL_mul_of_sl_jK_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (A B : _root_.GlobalTheory.KZ.GQ)
    (h : X.sl A X.jK = X.sl B X.jK) :
    ∃ (σ : SL(2, ℤ)) (c : ℚ), ((A : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      c • (((_root_.GlobalTheory.KZ.ofSL σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        ((B : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) := by
  obtain ⟨σ₁, T₁, h₁, rfl⟩ := exists_ofSL_mul_upperTriangular A
  obtain ⟨σ₂, T₂, h₂, rfl⟩ := exists_ofSL_mul_upperTriangular B
  have hT : X.sl T₁ X.jK = X.sl T₂ X.jK := by
    simpa [_root_.GlobalTheory.KZ.Tower.sl_mul,
      _root_.GlobalTheory.KZ.Tower.j_inv] using h
  obtain ⟨hρ, k, hk⟩ := entry_ratios_eq_of_upperTriangular_sl_jK_eq X T₁ T₂ h₁ h₂ hT
  obtain ⟨hd₁, ha₁, -⟩ := diag_ne_zero_and_ratio_pos_of_upperTriangular T₁ h₁
  obtain ⟨hd₂, ha₂, -⟩ := diag_ne_zero_and_ratio_pos_of_upperTriangular T₂ h₂
  let U : SL(2, ℤ) := ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨σ₁ * U * σ₂⁻¹, _root_.GlobalTheory.KZ.ent T₁ 1 1 / _root_.GlobalTheory.KZ.ent T₂ 1 1, ?_⟩
  have hT₁ : ((T₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (_root_.GlobalTheory.KZ.ent T₁ 1 1 / _root_.GlobalTheory.KZ.ent T₂ 1 1) •
        (((_root_.GlobalTheory.KZ.ofSL U : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
          ((T₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) := by
    unfold _root_.GlobalTheory.KZ.ent at *
    have hρ' := (div_eq_div_iff hd₁ hd₂).1 hρ
    have hk' : ((T₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1 *
        ((T₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 =
        ((T₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 *
          (((T₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1 +
            ((T₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 * k) := by
      field_simp at hk
      linear_combination hk
    have hU : ((_root_.GlobalTheory.KZ.ofSL U : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        !![1, (k : ℚ); 0, 1] := by
      ext i j
      rw [ofSL_apply]
      fin_cases i <;> fin_cases j <;> simp [U]
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h₁, h₂] <;>
      field_simp
    · linear_combination hρ'
    · linear_combination hk'
  have hgrp : _root_.GlobalTheory.KZ.ofSL (σ₁ * U * σ₂⁻¹) * (_root_.GlobalTheory.KZ.ofSL σ₂ * T₂) =
      _root_.GlobalTheory.KZ.ofSL σ₁ * (_root_.GlobalTheory.KZ.ofSL U * T₂) := by
    simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  rw [show ((_root_.GlobalTheory.KZ.ofSL (σ₁ * U * σ₂⁻¹) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      ((_root_.GlobalTheory.KZ.ofSL σ₂ * T₂ : _root_.GlobalTheory.KZ.GQ) : GL (Fin 2) ℚ) =
      ((_root_.GlobalTheory.KZ.ofSL (σ₁ * U * σ₂⁻¹) * (_root_.GlobalTheory.KZ.ofSL σ₂ * T₂) : _root_.GlobalTheory.KZ.GQ) :
        GL (Fin 2) ℚ) from rfl, hgrp]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hT₁, Matrix.mul_smul]

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma det_ofSL_eq_one (σ : SL(2, ℤ)) :
    Matrix.det ((_root_.GlobalTheory.KZ.ofSL σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  have h := σ.2
  rw [Matrix.det_fin_two] at h ⊢
  simp only [ofSL_apply]
  exact_mod_cast h

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma exists_smul_ofSL_mul_of_mul_ofSL {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (G : _root_.GlobalTheory.KZ.GQ)
    (γ : SL(2, ℤ))
    (h : X.sl (_root_.GlobalTheory.KZ.ofSL γ)
      (X.sl G X.jK) = X.sl G X.jK) :
    ∃ (σ : SL(2, ℤ)) (c : ℚ), (c = 1 ∨ c = -1) ∧
      ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        ((_root_.GlobalTheory.KZ.ofSL γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      c • (((_root_.GlobalTheory.KZ.ofSL σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) := by
  rw [← _root_.GlobalTheory.KZ.Tower.sl_mul] at h
  obtain ⟨σ, c, hc⟩ := exists_smul_ofSL_mul_of_sl_jK_eq X _ _ h
  refine ⟨σ, c, ?_, hc⟩
  have hdet := congrArg Matrix.det hc
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, Matrix.det_smul,
    det_ofSL_eq_one, Fintype.card_fin, one_mul] at hdet
  have hG : Matrix.det ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) ≠ 0 := G.2.ne'
  have h3 : (c * c - 1) * Matrix.det ((G : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = 0 := by
    linear_combination -hdet
  exact mul_self_eq_one_iff.1 (sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hG))

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma natCast_dvd_of_eq_sign_mul {x y : ℤ} {m : ℕ} {c : ℚ} (hc : c = 1 ∨ c = -1)
    (h : (x : ℚ) = c * (y * m)) : (m : ℤ) ∣ x := by
  rcases hc with rfl | rfl
  · refine ⟨y, ?_⟩
    have h' : (x : ℚ) = ((m : ℤ) : ℚ) * (y : ℚ) := by push_cast; linarith
    exact_mod_cast h'
  · refine ⟨-y, ?_⟩
    have h' : (x : ℚ) = ((m : ℤ) : ℚ) * ((-y : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h'

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in

theorem _root_.GlobalTheory.KZ.ES.Scal.lev_and_scalar : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε), ∀ m : ℕ, 0 < m → (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), _root_.GlobalTheory.KZ.ES.Lev X m (X.sl (_root_.GlobalTheory.KZ.toGQ g) X.jK)) ∧ ∀ γ : SL(2, ℤ), (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), X.sl (_root_.GlobalTheory.KZ.ofSL γ) (X.sl (_root_.GlobalTheory.KZ.toGQ g) X.jK) = X.sl (_root_.GlobalTheory.KZ.toGQ g) X.jK) → (_root_.GlobalTheory.KZ.en γ 0 1 : ZMod m) = 0 ∧ (_root_.GlobalTheory.KZ.en γ 1 0 : ZMod m) = 0 ∧ (_root_.GlobalTheory.KZ.en γ 0 0 : ZMod m) = _root_.GlobalTheory.KZ.en γ 1 1 := by
  intro Ω _ _ _ ε X m hm
  haveI : NeZero m := ⟨hm.ne'⟩
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hd1 : 0 < (!![(m : ℤ), 0; 0, 1]).det := by rw [Matrix.det_fin_two_of]; simpa using hm'
  have hd2 : 0 < (!![1, 0; 0, (m : ℤ)]).det := by rw [Matrix.det_fin_two_of]; simpa using hm'
  have hd3 : 0 < (!![1, 1; 0, (m : ℤ)]).det := by rw [Matrix.det_fin_two_of]; simpa using hm'
  refine ⟨?_, ?_⟩
  · intro g hg
    unfold _root_.GlobalTheory.KZ.ES.Lev
    intro γ hγ
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    obtain ⟨h00, h01, h10, h11⟩ := hγ
    have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := γ.2
      rwa [Matrix.det_fin_two] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 h10
      refine sl_ofSL_sl_jK_eq_of_mul_eq_intMatrix_mul X _ γ (!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
        m * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1; c', (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1]) (by
          rw [Matrix.det_fin_two_of]
          linear_combination hdet + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc') ?_
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ofSL_apply, Matrix.map_apply,
          toGQ_apply _ hd1, hc'] <;> ring
    · obtain ⟨b', hb'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 h01
      refine sl_ofSL_sl_jK_eq_of_mul_eq_intMatrix_mul X _ γ (!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, b';
        m * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1]) (by
          rw [Matrix.det_fin_two_of]
          linear_combination hdet + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * hb') ?_
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ofSL_apply, Matrix.map_apply,
          toGQ_apply _ hd2, hb'] <;> ring
    · have hz : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
          (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod m) = 0 := by
        push_cast
        rw [h00, h01, h10, h11]
        ring
      obtain ⟨e', he'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 hz
      refine sl_ofSL_sl_jK_eq_of_mul_eq_intMatrix_mul X _ γ (!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
        (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, e'; m * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
        (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0]) (by
          rw [Matrix.det_fin_two_of]
          linear_combination hdet + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * he') ?_
      have he'' : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℚ) = (m : ℚ) * e' -
          (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
            (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
        have := congrArg (fun z : ℤ => (z : ℚ)) he'
        push_cast at this
        linear_combination this
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ofSL_apply, Matrix.map_apply,
          toGQ_apply _ hd3, he''] <;> ring
  · intro γ hfix
    obtain ⟨σ₁, c₁, hc₁, e₁⟩ := exists_smul_ofSL_mul_of_mul_ofSL X _ γ (hfix !![(m : ℤ), 0; 0, 1] (by simp))
    obtain ⟨σ₂, c₂, hc₂, e₂⟩ := exists_smul_ofSL_mul_of_mul_ofSL X _ γ (hfix !![1, 0; 0, (m : ℤ)] (by simp))
    obtain ⟨σ₃, c₃, hc₃, e₃⟩ := exists_smul_ofSL_mul_of_mul_ofSL X _ γ (hfix !![1, 1; 0, (m : ℤ)] (by simp))
    have E₁ := congrFun (congrFun e₁ 1) 0
    have E₂ := congrFun (congrFun e₂ 0) 1
    have E₃a := congrFun (congrFun e₃ 0) 0
    have E₃b := congrFun (congrFun e₃ 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, ofSL_apply,
      toGQ_apply _ hd1] at E₁
    simp [Matrix.mul_apply, Fin.sum_univ_two, ofSL_apply,
      toGQ_apply _ hd2] at E₂
    simp [Matrix.mul_apply, Fin.sum_univ_two, ofSL_apply,
      toGQ_apply _ hd3] at E₃a E₃b
    have hdiv₁ : (m : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
      natCast_dvd_of_eq_sign_mul (y := (σ₁ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) hc₁ (by linear_combination E₁)
    have hdiv₂ : (m : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
      natCast_dvd_of_eq_sign_mul (y := (σ₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) hc₂ (by linear_combination E₂)
    have hdiv₃ : (m : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
      natCast_dvd_of_eq_sign_mul (y := (σ₃ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) hc₃
        (by push_cast; linear_combination E₃b - E₃a)
    have z₁ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).2 hdiv₁
    have z₂ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).2 hdiv₂
    have z₃ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).2 hdiv₃
    push_cast at z₃
    refine ⟨z₂, z₁, ?_⟩
    change (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod m) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod m)
    linear_combination -z₃ + z₂ - z₁

end GlobalTheory.KZ.ES.Scal
