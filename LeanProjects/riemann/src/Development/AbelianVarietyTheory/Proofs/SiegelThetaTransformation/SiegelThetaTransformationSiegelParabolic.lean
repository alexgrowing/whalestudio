import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInvariantIntegralMatrixMulStatement

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.Parab

theorem par_exists_den {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, IsIntegral ℤ (((N : ℚ) • S) i j) := by
  classical
  refine ⟨∏ p : ι × ι, (S p.1 p.2).den, Finset.prod_pos fun p _ => (S p.1 p.2).den_pos, ?_⟩
  intro i j
  obtain ⟨c, hc⟩ : (S i j).den ∣ ∏ p : ι × ι, (S p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : ι × ι => (S p.1 p.2).den) (Finset.mem_univ (i, j))
  rw [hc, Matrix.smul_apply, smul_eq_mul]
  have : (((S i j).den * c : ℕ) : ℚ) * S i j = algebraMap ℤ ℚ (c * (S i j).num) := by
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← Rat.mul_den_eq_num (S i j)]
    ring
  rw [this]
  exact isIntegral_algebraMap

noncomputable def parChar {κ ι : Type} [Fintype κ] [Fintype ι] (S : Matrix ι ι ℚ)
    (x : Matrix κ ι ℚ) : ℂ :=
  cexp (-(Real.pi * I * ((∑ k, x k ⬝ᵥ S *ᵥ x k : ℚ) : ℂ)))

open Matrix Complex in
open scoped ComplexConjugate Real in
lemma _root_.GlobalTheory.SW.Parab.parChar_mul_conj {κ ι : Type} [Fintype κ] [Fintype ι]
    (S : Matrix ι ι ℚ) (x : Matrix κ ι ℚ) :
    _root_.GlobalTheory.SW.Parab.parChar S x * conj (_root_.GlobalTheory.SW.Parab.parChar S x) = 1 := by
  unfold _root_.GlobalTheory.SW.Parab.parChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp [Complex.conj_I, map_ratCast]

open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma exists_pos_nat_mul_eq_int {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ T : Matrix ι ι ℤ, ∀ i j, (T i j : ℚ) = d * S i j := by
  refine ⟨∏ i, ∏ j, (S i j).den, Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (S i j).den_pos, ?_⟩
  have key : ∀ i j, ∃ t : ℤ, (t : ℚ) = ((∏ i, ∏ j, (S i j).den : ℕ) : ℚ) * S i j := by
    intro i j
    obtain ⟨m, hm⟩ : (S i j).den ∣ ∏ i, ∏ j, (S i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (S i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (S i j).den) (Finset.mem_univ i))
    refine ⟨m * (S i j).num, ?_⟩
    rw [hm]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose T hT using key
  exact ⟨T, hT⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma isIntegral_int_rat_iff_exists_int (q : ℚ) : IsIntegral ℤ q ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  simp

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.isSB_parChar_mul {κ ι : Type} [Fintype κ] [Fintype ι] (S : Matrix ι ι ℚ)
    (φ : Matrix κ ι ℚ → ℂ) (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB fun x => _root_.GlobalTheory.SW.Parab.parChar S x * φ x := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  obtain ⟨d, hd, T, hT⟩ := exists_pos_nat_mul_eq_int S
  refine ⟨2 * d * R, by positivity, ?_, ?_⟩
  · intro x hx
    have hint := hsupp x (right_ne_zero_of_mul hx)
    intro k i
    obtain ⟨n, hn⟩ := (isIntegral_int_rat_iff_exists_int _).1 (hint k i)
    refine (isIntegral_int_rat_iff_exists_int _).2 ⟨2 * d * n, ?_⟩
    simp only [Matrix.smul_apply, smul_eq_mul] at hn ⊢
    push_cast at hn ⊢
    linear_combination (2 * d : ℚ) * hn

  · intro x y hy
    have hy' : _root_.GlobalTheory.SW.IntM (((2 * d : ℕ) : ℚ) • y) := by
      intro k i
      obtain ⟨n, hn⟩ := (isIntegral_int_rat_iff_exists_int _).1 (hy k i)
      refine (isIntegral_int_rat_iff_exists_int _).2 ⟨2 * d * n, ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul]
      push_cast
      rw [hn]
    have hφ : φ (x + ((2 * d * R : ℕ) : ℚ) • y) = φ x := by
      rw [← hper x _ hy', smul_smul]
      push_cast
      ring_nf
    simp only
    rw [hφ]
    by_cases h0 : φ x = 0
    · simp [h0]
    congr 1
    have hU : ∀ k i, ∃ n : ℤ, (n : ℚ) = R * x k i := fun k i => by
      simpa using (isIntegral_int_rat_iff_exists_int _).1 (hsupp x h0 k i)
    choose U hU using hU
    have hY : ∀ k i, ∃ n : ℤ, (n : ℚ) = y k i := fun k i =>
      (isIntegral_int_rat_iff_exists_int _).1 (hy k i)
    choose Y hY using hY
    have hQ : ∑ k, (x + ((2 * d * R : ℕ) : ℚ) • y) k ⬝ᵥ S *ᵥ (x + ((2 * d * R : ℕ) : ℚ) • y) k =
        ∑ k, x k ⬝ᵥ S *ᵥ x k + 2 * ((∑ k, ∑ i, ∑ j, (U k i * T i j * Y k j + Y k i * T i j * U k j +
          2 * d * R ^ 2 * Y k i * T i j * Y k j) : ℤ) : ℚ) := by
      push_cast
      simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hR' : (R : ℚ) ≠ 0 := by positivity
      have hd' : (d : ℚ) ≠ 0 := by positivity
      have hx1 : x k i = U k i / R := by rw [hU]; field_simp
      have hx2 : x k j = U k j / R := by rw [hU]; field_simp
      have hS : S i j = T i j / d := by rw [hT]; field_simp
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      rw [hx1, hx2, hS, ← hY k i, ← hY k j]
      field_simp
      ring
    unfold _root_.GlobalTheory.SW.Parab.parChar
    rw [hQ]
    set m : ℤ := ∑ k, ∑ i, ∑ j, (U k i * T i j * Y k j + Y k i * T i j * U k j +
          2 * d * R ^ 2 * Y k i * T i j * Y k j)
    have : -(↑π * I * (((∑ k, x k ⬝ᵥ S *ᵥ x k + 2 * (m : ℚ) : ℚ)) : ℂ)) =
        -(↑π * I * ((∑ k, x k ⬝ᵥ S *ᵥ x k : ℚ) : ℂ)) + ((-m : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.qv_row_mul {κ ι : Type} [Fintype ι] (x : Matrix κ ι ℚ) (A : Matrix ι ι ℚ) (k : κ) :
    _root_.GlobalTheory.SW.qv ((x * A) k) = _root_.GlobalTheory.SW.qv (x k) ᵥ* _root_.GlobalTheory.SW.qm A := by
  funext j
  simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.qm, vecMul, dotProduct, mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.qv_bilin {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) (v : ι → ℚ) :
    ((v ⬝ᵥ S *ᵥ v : ℚ) : ℂ) = _root_.GlobalTheory.SW.qv v ⬝ᵥ _root_.GlobalTheory.SW.qm S *ᵥ _root_.GlobalTheory.SW.qv v := by
  simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.qm, mulVec, dotProduct]

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.qm_mul' {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (A * B) = _root_.GlobalTheory.SW.qm A * _root_.GlobalTheory.SW.qm B := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma parabolic_exponent_term_eq {ι : Type} [Fintype ι] (A B : Matrix ι ι ℚ) (τ : Matrix ι ι ℂ)
    (v : ι → ℚ) (z : ι → ℂ) :
    _root_.GlobalTheory.SW.qv v ⬝ᵥ ((_root_.GlobalTheory.SW.qm A * τ + _root_.GlobalTheory.SW.qm B) *
        _root_.GlobalTheory.SW.qm Aᵀ) *ᵥ _root_.GlobalTheory.SW.qv v +
      2 * _root_.GlobalTheory.SW.qv v ⬝ᵥ (z ᵥ* _root_.GlobalTheory.SW.qm Aᵀ) =
    (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) ⬝ᵥ τ *ᵥ
        (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) +
      2 * (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) ⬝ᵥ z +
      ((v ⬝ᵥ (B * Aᵀ) *ᵥ v : ℚ) : ℂ) := by
  rw [_root_.GlobalTheory.SW.Parab.qv_bilin, _root_.GlobalTheory.SW.Parab.qm_mul']
  have hT : _root_.GlobalTheory.SW.qm Aᵀ = (_root_.GlobalTheory.SW.qm A)ᵀ := by
    ext i j
    simp [_root_.GlobalTheory.SW.qm]
  rw [hT, add_mul, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose,
    dotProduct_mulVec, vecMul_transpose, dotProduct_mulVec _ (_root_.GlobalTheory.SW.qm A) z]
  ring

open Matrix Complex in
open scoped ComplexConjugate Real in

theorem _root_.GlobalTheory.SW.Parab.trans_parabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ →
    σ.toBlocks₂₁ = 0 → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, _root_.GlobalTheory.SW.IsSB φ →
    _root_.GlobalTheory.SW.IsSB (ω φ) ∧ _root_.GlobalTheory.SW.TransS σ φ (ω φ) ∧
    ∀ φ', _root_.GlobalTheory.SW.IsSB φ' → _root_.GlobalTheory.SW.ip (ω φ) (ω φ') =
      _root_.GlobalTheory.SW.ip φ φ' := by
  intro κ ι _ _ _ σ hev hσ hC
  classical
  have hDA : σ.toBlocks₂₂ * σ.toBlocks₁₁ᵀ = 1 := by
    have h := hσ
    rw [SymplecticGroup.mem_iff, ← fromBlocks_toBlocks σ, hC] at h
    simp only [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at h
    simpa using h.2.2.1
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hAD : Aᵀ * D = 1 := mul_eq_one_comm.mp hDA
  have hDtA : Dᵀ * A = 1 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hAD
  have hADt : A * Dᵀ = 1 := mul_eq_one_comm.mp hDtA
  have hdet : D.det * A.det = 1 := by
    have h := congrArg Matrix.det hDA
    rwa [det_mul, det_transpose, det_one] at h
  have hdetA : A.det ≠ 0 := fun h => by simp [h] at hdet
  let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
    { toFun := fun x => x * A
      invFun := fun x => x * Dᵀ
      left_inv := fun x => by simp [Matrix.mul_assoc, hADt]
      right_inv := fun x => by simp [Matrix.mul_assoc, hDtA] }
  let c : ℂ := (_root_.GlobalTheory.SW.qm D).det ^ (Fintype.card κ / 2)
  refine ⟨fun φ => c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ (x * A), fun φ hφ => ?_⟩
  have hφA := (_root_.GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hdetA
  have hf := _root_.GlobalTheory.SW.Parab.isSB_parChar_mul (B * Aᵀ) _ hφA.1
  refine ⟨(_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hf hf).2.1 c, ?_, ?_⟩
  · intro τ hτ ζ
    have hqD : (_root_.GlobalTheory.SW.qm D)⁻¹ = _root_.GlobalTheory.SW.qm Aᵀ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [← _root_.GlobalTheory.SW.Parab.qm_mul', hDA]
      ext i j
      by_cases hij : i = j <;> simp [_root_.GlobalTheory.SW.qm, one_apply, hij]
    have h0 : _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ = 0 := by
      rw [hC]
      ext i j
      simp [_root_.GlobalTheory.SW.qm]
    unfold _root_.GlobalTheory.SW.thS _root_.GlobalTheory.SW.spAct _root_.GlobalTheory.SW.spDen
    rw [h0, ← hA, ← hB, ← hD]
    simp only [zero_mul, zero_add, Matrix.mul_zero, zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one, hqD, Pi.smul_apply, smul_eq_mul]
    conv_rhs => rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext x
    simp only [e, Equiv.coe_fn_mk, _root_.GlobalTheory.SW.Parab.qv_row_mul, parabolic_exponent_term_eq,
      Finset.sum_add_distrib]
    unfold _root_.GlobalTheory.SW.Parab.parChar
    rw [Rat.cast_sum, mul_add, Complex.exp_add, Complex.exp_neg]
    field_simp
    exact mul_comm _ _
  · intro φ' hφ'
    have hconj := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι φ' φ' hφ' hφ').2.2.2.1
    have hg : _root_.GlobalTheory.SW.IsSB fun x => φ x * conj (φ' x) :=
      (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hφ hconj).2.2.1
    have hgA := (_root_.GlobalTheory.SW.LinChange.haar_mul ℚ κ ι _ hg).1 A hdetA
    have hgA' := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hgA.1 hgA.1).2.2.2.2.2.1
    unfold _root_.GlobalTheory.SW.ip
    have hpt : (fun x => (c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ (x * A)) x *
        conj ((c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ' (x * A)) x)) =
        (c * conj c) • fun x => φ (x * A) * conj (φ' (x * A)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (c * conj c * φ (x * A) * conj (φ' (x * A))) *
        _root_.GlobalTheory.SW.Parab.parChar_mul_conj (B * Aᵀ) x
    rw [hpt, hgA', hgA.2, ← mul_assoc]
    have hdetD : (_root_.GlobalTheory.SW.qm D).det = (D.det : ℂ) := by
      rw [_root_.GlobalTheory.SW.qm]
      exact ((Rat.castHom ℂ).map_det D).symm
    obtain ⟨r, hr⟩ := hev
    have hn : Fintype.card κ / 2 = r := by omega
    have hq : (D.det ^ r * D.det ^ r * |A.det| ^ (r + r) : ℚ) = 1 := by
      rw [Even.pow_abs ⟨r, rfl⟩, ← pow_add, ← mul_pow, hdet, one_pow]
    have hconst : ∀ N : ℚ, N = A.det → c * conj c * ((|N| : ℚ) : ℂ) ^ Fintype.card κ = 1 := by
      rintro N rfl
      simp only [c, hdetD, hn, map_pow, map_ratCast]
      rw [hr]
      exact_mod_cast hq
    rw [hconst _ ?_, one_mul]
    exact congrFun (congrArg DFunLike.coe (Algebra.norm_self ℚ)) A.det

end GlobalTheory.SW.Parab
