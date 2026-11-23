import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesRing
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

namespace IntSeriesNorm

theorem intSeriesEval_one (z : ℂ) : intSeriesEval 1 z = 1 := by
  rw [intSeriesEval, tsum_eq_single 0]
  · simp
  · intro n hn; simp [coeff_one, hn]

theorem intSeriesEval_X (z : ℂ) : intSeriesEval X z = z := by
  rw [intSeriesEval, tsum_eq_single 1]
  · simp
  · intro n hn; simp [coeff_X, hn]

theorem intSeriesConv_X (r : ℝ) : IntSeriesConv X r := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_X, hn]

def residuePart (F : PowerSeries ℤ) (p i : ℕ) : PowerSeries ℤ :=
  mk fun m ↦ coeff (m * p + i) F

theorem residuePart_conv {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r) (hF : IntSeriesConv F r)
    {p : ℕ} (hp : 0 < p) (i : ℕ) : IntSeriesConv (residuePart F p i) (r ^ p) := by
  unfold IntSeriesConv at *
  have hinj : Function.Injective fun m : ℕ ↦ m * p + i := fun a b h ↦
    Nat.eq_of_mul_eq_mul_right hp (Nat.add_right_cancel h)
  have h1 := (hF.comp_injective hinj).mul_left ((r ^ i)⁻¹)
  refine h1.congr fun m ↦ ?_
  have hri : r ^ i ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [Function.comp_apply, residuePart, coeff_mk]
  rw [pow_add, pow_mul']
  field_simp

theorem intSeriesEval_split (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ}
    (hr : 0 < r) (hF : IntSeriesConv F r) {p : ℕ} (hp : 0 < p) (s : ℂ) (hs : ‖s‖ ≤ r) :
    intSeriesEval F s = ∑ i : Fin p, s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p) := by
  have : NeZero p := ⟨hp.ne'⟩
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hsum := (hR r hr.le).2.2.1 F hF s hs
  have hparts : ∀ i : Fin p, HasSum (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i))
      (s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p)) := by
    intro i
    have h := ((hR (r ^ p) (pow_nonneg hr.le p)).2.2.1 _ (residuePart_conv hr hF hp i) _ hq).mul_left
      (s ^ (i : ℕ))
    have hf : (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i)) =
        fun m ↦ s ^ (i : ℕ) * (((coeff m (residuePart F p i) : ℤ) : ℂ) * (s ^ p) ^ m) := by
      funext m
      simp only [residuePart, coeff_mk]
      rw [pow_add, pow_mul']
      ring
    rw [hf]
    exact h
  let e : ℕ ≃ Fin p × ℕ := (Nat.divModEquiv p).trans (Equiv.prodComm _ _)
  have hfe : ∀ x : Fin p × ℕ, e.symm x = x.2 * p + x.1 := fun x ↦ rfl
  have htot := (e.symm.hasSum_iff).mpr hsum
  simp only [Function.comp_def, hfe] at htot
  exact (htot.prod_fiberwise hparts).unique (hasSum_fintype _)

def evalHom (S : Subring (PowerSeries ℤ)) (z : ℂ)
    (hmul : ∀ F G : S, intSeriesEval ((F : PowerSeries ℤ) * G) z =
      intSeriesEval F z * intSeriesEval G z)
    (hhas : ∀ F : S, HasSum (fun n ↦ ((coeff n (F : PowerSeries ℤ) : ℤ) : ℂ) * z ^ n)
      (intSeriesEval F z)) : S →+* ℂ where
  toFun f := intSeriesEval f z
  map_one' := by simp only [Subring.coe_one, intSeriesEval_one]
  map_mul' F G := by simp only [Subring.coe_mul]; exact hmul F G
  map_zero' := by simp [intSeriesEval]
  map_add' F G := by
    have h := hhas (F + G)
    simp only [Subring.coe_add, map_add, Int.cast_add, add_mul] at h
    exact h.unique ((hhas F).add (hhas G))

def normMatrix (F : PowerSeries ℤ) (p : ℕ) [NeZero p] : Matrix (Fin p) (Fin p) (PowerSeries ℤ) :=
  Matrix.of fun i k ↦ (if i ≤ k then 1 else X) * residuePart F p ((k - i : Fin p) : ℕ)

theorem normMatrix_row (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r)
    (hF : IntSeriesConv F r) {p : ℕ} [NeZero p] (s : ℂ) (hs : ‖s‖ ≤ r) (i : Fin p) :
    ∑ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) * s ^ (k : ℕ) =
      s ^ (i : ℕ) * intSeriesEval F s := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨-, hmul, -, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hentry : ∀ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) =
      (if i ≤ k then 1 else s ^ p) * intSeriesEval (residuePart F p ((k - i : Fin p) : ℕ)) (s ^ p) := by
    intro k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, one_mul]
    · rw [hmul _ _ (intSeriesConv_X _) (residuePart_conv hr hF hp _) _ hq, intSeriesEval_X]
  rw [intSeriesEval_split hR hr hF hp s hs, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.addLeft i)
  intro k
  simp only [Equiv.coe_addLeft]
  rw [hentry, add_sub_cancel_left]
  have hi := i.is_lt
  have hk := k.is_lt
  by_cases h : (i : ℕ) + k < p
  · have hv : ((i + k : Fin p) : ℕ) = i + k := by rw [Fin.val_add, Nat.mod_eq_of_lt h]
    have hle : i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_pos hle, hv, pow_add]
    ring
  · have hv : ((i + k : Fin p) : ℕ) = i + k - p := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hnle : ¬ i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_neg hnle, hv]
    have hpow : s ^ ((i : ℕ) + k) = s ^ p * s ^ ((i : ℕ) + k - p) := by
      rw [← pow_add]; congr 1; omega
    generalize intSeriesEval (residuePart F p k) (s ^ p) = G
    calc s ^ (i : ℕ) * (s ^ (k : ℕ) * G) = s ^ ((i : ℕ) + k) * G := by rw [pow_add]; ring
      _ = _ := by rw [hpow]; ring

theorem proof (hR : IntSeriesRing.Statement) : IntSeriesNorm.Statement := by
  intro F r hr hF p hp j
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨⟨S, hS⟩, hmul, hhas, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  by_cases hj : p < j
  · refine ⟨0, ?_, fun t _ _ ↦ ?_⟩
    · simp [IntSeriesConv]
    · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hj)]
      simp [intSeriesEval]
  push Not at hj
  have hmem : ∀ i k, normMatrix F p i k ∈ S := by
    intro i k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, hS]; exact residuePart_conv hr hF hp _
    · exact S.mul_mem ((hS _).2 (intSeriesConv_X _)) ((hS _).2 (residuePart_conv hr hF hp _))
  let M : Matrix (Fin p) (Fin p) S := Matrix.of fun i k ↦ ⟨normMatrix F p i k, hmem i k⟩
  let e : S := (-1) ^ j * M.charpoly.coeff (p - j)
  refine ⟨e, (hS _).1 e.2, fun t ht htr ↦ ?_⟩
  have hq : ‖t ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) htr p
  let φ : S →+* ℂ := evalHom S (t ^ p)
    (fun F G ↦ hmul F G ((hS _).1 F.2) ((hS _).1 G.2) _ hq) (fun F ↦ hhas F ((hS _).1 F.2) _ hq)
  have hφ : ∀ f : S, φ f = intSeriesEval f (t ^ p) := fun _ ↦ rfl
  set ζ := Complex.exp (2 * π * Complex.I / p) with hζdef
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne'
  have hexp : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * a / p) = ζ ^ a := by
    intro a; rw [hζdef, ← Complex.exp_nat_mul]; congr 1; ring
  let v : Fin p → ℂ := fun a ↦ ζ ^ (a : ℕ) * t
  have hvnorm : ∀ a, ‖v a‖ ≤ r := by
    intro a; simpa [v, norm_pow, hζ.norm'_eq_one hp.ne'] using htr
  have hvpow : ∀ a, v a ^ p = t ^ p := by
    intro a
    simp only [v]
    rw [mul_pow, ← pow_mul, mul_comm (a : ℕ) p, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hvinj : Function.Injective v := by
    intro a b hab
    exact Fin.ext (hζ.pow_inj a.is_lt b.is_lt (mul_right_cancel₀ ht hab))
  let d : Fin p → ℂ := fun a ↦ intSeriesEval F (v a)
  let A := M.map φ
  have hA : ∀ i k, A i k = intSeriesEval (normMatrix F p i k) (t ^ p) := fun _ _ ↦ rfl
  let V := (Matrix.vandermonde v).transpose
  have hAV : A * V = V * Matrix.diagonal d := by
    ext i a
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [V, Matrix.transpose_apply, Matrix.vandermonde_apply, hA]
    rw [← hvpow a]
    exact normMatrix_row hR hr hF (v a) (hvnorm a) i
  have hdet : IsUnit V.det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hvinj
  have hchar : A.charpoly = (Matrix.diagonal d).charpoly := by
    have hconj : A = V * Matrix.diagonal d * V⁻¹ := by
      rw [← hAV, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    rw [hconj, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]
  have hmset : (Multiset.range p).map (fun a : ℕ ↦
      intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)) =
      (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) :=
    Multiset.map_congr rfl fun a _ ↦ by rw [hexp]
  rw [hmset]
  set m := (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) with hm
  have hcard : Multiset.card m = p := by simp [hm]
  have hprod : (m.map fun x ↦ Polynomial.X - Polynomial.C x).prod = A.charpoly := by
    rw [hchar, Matrix.charpoly_diagonal]
    refine (((Fin.prod_univ_eq_prod_range
      (fun a : ℕ ↦ Polynomial.X - Polynomial.C (intSeriesEval F (ζ ^ a * t))) p)).trans ?_).symm
    rw [hm, Multiset.map_map]
    rfl
  have hcoef := Multiset.prod_X_sub_C_coeff m (k := p - j) (by omega)
  rw [hcard, Nat.sub_sub_self hj, hprod] at hcoef
  have heval : intSeriesEval (e : PowerSeries ℤ) (t ^ p) = (-1) ^ j * A.charpoly.coeff (p - j) := by
    rw [← hφ]
    show φ ((-1) ^ j * M.charpoly.coeff (p - j)) = _
    rw [map_mul, map_pow, map_neg, map_one, ← Polynomial.coeff_map, ← Matrix.charpoly_map]
  rw [heval, hcoef, ← mul_assoc, ← mul_pow]
  simp

end IntSeriesNorm

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
