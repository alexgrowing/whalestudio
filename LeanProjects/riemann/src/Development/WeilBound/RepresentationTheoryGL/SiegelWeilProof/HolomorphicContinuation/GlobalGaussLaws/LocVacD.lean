import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacA

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {m n : ℕ}

def sR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem gramX_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX ε x j i = ∑ a, (sR ε a : ℂ) * (star (x a j) * x a i) := by
  simp only [gramX, Qp, Qb, evX, sR, map_sub, map_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

theorem trace_eq (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
  have h1 : (b * gramX ε x).trace = ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h1]
  calc ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i)
      = ∑ i, ∑ a, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := Finset.sum_comm
    _ = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
        simp only [Finset.mul_sum]

theorem secN_one (ε : Fin m → Bool) (c t : ℝ) (hc : 0 < c) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b =
      ∏ a : Fin m, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det := by
  have hpt : ∀ x : Fin m → Fin n → ℂ,
      evX (1 : PX m n) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
        = ∏ a, rowF c (t * sR ε a) b (x a) := by
    intro x
    simp only [evX, map_one, one_mul, gs, rowF, trace_eq, Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    · congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · congr 1
      rw [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
  unfold secN
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a v => rowF c (t * sR ε a) b v)]
  exact Finset.prod_congr rfl fun a _ => row_int c _ hc b hb

theorem detpm (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b = (c : ℂ) • (1 - (Complex.I * (s : ℂ)) • b) := by
  rw [smul_sub, smul_smul]; push_cast; congr 2; ring

theorem fac_eq (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b).det =
      ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) * ((1 - (Complex.I * (s : ℂ)) • b).det)⁻¹ := by
  rw [detpm, det_smul, Fintype.card_fin, div_mul_eq_div_div, div_eq_mul_inv]

theorem one_sub_neg (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((-1 : ℝ) : ℂ)) • b) = 1 + Complex.I • b := by
  push_cast; rw [mul_neg_one, neg_smul, sub_neg_eq_add]

theorem one_sub_pos (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((1 : ℝ) : ℂ)) • b) = 1 - Complex.I • b := by
  push_cast; rw [mul_one]

private theorem prod_bool_fun_eq_pow_cnt_mul_pow_cnt (ε : Fin m → Bool) (F : Bool → ℂ) :
    ∏ a, F (ε a) = F true ^ cnt ε true * F false ^ cnt ε false := by
  have h : ∀ a, F (ε a) = if ε a = true then F true else F false := by
    intro a
    cases ε a <;> simp
  rw [Finset.prod_congr rfl fun a _ => h a, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp [cnt]

theorem secN_eval (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (hc : 0 < c)
    (hsign : (t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true))
    (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b = ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) *
      (1 - Complex.I • b).det ^ (-(p : ℤ)) * (1 + Complex.I • b).det ^ (-(q : ℤ)) := by
  rw [secN_one ε c t hc b hb]
  rcases hsign with ⟨ht, hp, hq⟩ | ⟨ht, hp, hq⟩
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then 1 else -1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      rw [ht, fac_eq]
      rfl
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then -1 else 1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      have hs : t * sR ε a = c * (if ε a = true then -1 else 1) := by
        rw [ht]
        unfold sR
        split_ifs <;> ring
      rw [hs, fac_eq]
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring

end PositivityTheory.Rg.Sw.Glob.Vac
