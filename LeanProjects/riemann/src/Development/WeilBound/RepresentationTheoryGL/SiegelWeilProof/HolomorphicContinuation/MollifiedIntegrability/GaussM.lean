import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

noncomputable section

open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

namespace GM

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  apply Complex.ext <;> simp [herm] <;> ring

theorem gramX_isHermitian (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x).IsHermitian := by
  ext i j
  simp only [gramX, Qp, Qb, evX, conjTranspose_apply, map_sub, map_sum, map_mul, eval_X, star_sub, star_sum,
    star_mul', star_star]
  simp only [if_true, Bool.false_eq_true, if_false]
  congr 1 <;> (refine Finset.sum_congr rfl fun a _ => ?_; rw [star_star, mul_comm])

theorem trace_im_zero {b Q : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (hQ : Q.IsHermitian) :
    (b * Q).trace.im = 0 := by
  have h : star (b * Q).trace = (b * Q).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hb.eq, hQ.eq, Matrix.trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem norm_phase {ε : Fin m → Bool} {t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have h0 := trace_im_zero hb (gramX_isHermitian ε x)
  have : (Complex.I * t * (b * gramX ε x).trace).re = 0 := by
    simp [Complex.mul_re, h0]
  rw [this, Real.exp_zero]

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  unfold evX
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
  · exact (continuous_apply _).comp (continuous_apply _)

theorem integ_sec (hI : IntegP) {ε : Fin m → Bool} {c t : ℝ} (hc : 0 < c) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (P : PX m n) :
    Integrable fun x => evX P x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := by
  refine (hI m n c hc P).mono ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hI m n c hc P).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    refine (continuous_const.matrix_mul ?_).matrix_trace
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_evX _
  · rw [norm_mul, norm_phase hb, mul_one]

theorem sec_add (hI : IntegP) {ε : Fin m → Bool} {c t : ℝ} (hc : 0 < c) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (P Q : PX m n) : secN ε c t (P + Q) b = secN ε c t P b + secN ε c t Q b := by
  unfold secN
  rw [← integral_add (integ_sec hI hc hb P) (integ_sec hI hc hb Q)]
  congr 1; funext x; simp [evX]; ring

theorem sec_smul {ε : Fin m → Bool} {c t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (r : ℂ) (P : PX m n) :
    secN ε c t (r • P) b = r * secN ε c t P b := by
  unfold secN
  rw [← integral_const_mul]
  congr 1; funext x; simp [evX, smul_eq_C_mul]; ring

theorem sec_zero {ε : Fin m → Bool} {c t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} : secN ε c t (0 : PX m n) b = 0 := by
  simp [secN, evX]

theorem star_dot_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
  have h1 : star (star v ⬝ᵥ (b *ᵥ v)) = star (b *ᵥ v) ⬝ᵥ v := by
    simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : star (b *ᵥ v) = star v ᵥ* b := by rw [star_mulVec, hb.eq]
  rw [h1, h2, dotProduct_mulVec]

theorem det_ne_zero {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (r : ℝ) :
    (1 - (Complex.I * r) • b).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have e1 : v = (Complex.I * r) • (b *ᵥ v) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec] at hMv
    exact sub_eq_zero.mp hMv
  have e2 : star v ⬝ᵥ v = (Complex.I * r) * (star v ⬝ᵥ (b *ᵥ v)) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ ((Complex.I * r) • (b *ᵥ v)) := by rw [← e1]
      _ = _ := by rw [dotProduct_smul, smul_eq_mul]
  have hq : (star v ⬝ᵥ (b *ᵥ v)).im = 0 := by
    have := congrArg Complex.im (star_dot_herm hb v)
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hs : (star v ⬝ᵥ v).im = 0 := by
    have : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by
      simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hr : (star v ⬝ᵥ v).re = 0 := by
    rw [e2]; simp [Complex.mul_re, hq]
  exact hv (dotProduct_star_self_eq_zero.mp (Complex.ext (by simpa using hr) (by simpa using hs)))

def sR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sR ε a : ℝ) : ℂ) := by
  unfold sgn sR; split_ifs <;> simp

def Mm (ε : Fin m → Bool) (s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  1 - (Complex.I * ((s * sR ε a : ℝ) : ℂ)) • b

theorem amat_eq (ε : Fin m → Bool) (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) :
    Amat ε c (s * c) b a = (c : ℂ) • (Mm ε s b a)ᵀ := by
  unfold Amat Mm
  rw [transpose_sub, transpose_one, transpose_smul, smul_sub, smul_smul, sgn_eq]
  congr 2
  push_cast; ring

theorem amat_inv_apply (ε : Fin m → Bool) {c : ℝ} (hc : c ≠ 0) (s : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) (i j : Fin n) :
    (Amat ε c (s * c) b a)⁻¹ j i = (c : ℂ)⁻¹ * ((Mm ε s b a)⁻¹) i j := by
  have hM : IsUnit (Mm ε s b a).det := isUnit_iff_ne_zero.mpr (det_ne_zero hb _)
  have hinv : (Amat ε c (s * c) b a)⁻¹ = (c : ℂ)⁻¹ • ((Mm ε s b a)⁻¹)ᵀ := by
    rw [amat_eq]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul,
      ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, transpose_one]
  rw [hinv]; simp

theorem amat_det (ε : Fin m → Bool) {c : ℝ} (hc : c ≠ 0) (s : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) :
    (Real.pi : ℂ) ^ n / (Amat ε c (s * c) b a).det = ((Real.pi : ℂ) / c) ^ n * ((Mm ε s b a)⁻¹).det := by
  have hM := det_ne_zero hb (s * sR ε a)
  rw [amat_eq, det_smul, det_transpose, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv']
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold Mm at hM ⊢
  rw [div_pow]
  field_simp

end GM

theorem mm_inv (ε : Fin m → Bool) (s : ℝ) (y : E n) (a : Fin m) :
    (GM.Mm ε s (herm y) a)⁻¹ = if ε a then uM (s : ℂ) y else vM (s : ℂ) y := by
  unfold GM.Mm GM.sR uM vM
  split_ifs with h
  · push_cast; rw [mul_one]
  · push_cast
    congr 1
    rw [show Complex.I * ((s : ℂ) * -1) = -(Complex.I * s) by ring, neg_smul, sub_neg_eq_add]

open GM in
theorem key (hI : IntegP) (hW : Wick) (hR : Rot) (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∀ P : PX m n, ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
      secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y := by

  let S : Submodule ℂ (PX m n) :=
    { carrier := {P | ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
        secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y}
      add_mem' := by
        rintro P Q ⟨R1, h1⟩ ⟨R2, h2⟩
        refine ⟨R1 + R2, fun y => ?_⟩
        rw [sec_add hI hc (herm_isHermitian y), h1, h2]
        simp [evUV, map_add]; ring
      zero_mem' := ⟨0, fun y => by simp [sec_zero, evUV]⟩
      smul_mem' := by
        rintro r P ⟨R1, h1⟩
        refine ⟨MvPolynomial.C r * R1, fun y => ?_⟩
        rw [sec_smul, h1]
        simp [evUV]; ring }
  have hmono : ∀ N : ℕ, ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, d.sum (fun _ e => e) = N → monomial d (1 : ℂ) ∈ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro d hd
      by_cases ht : ∃ k : Fin m × Fin n × Bool, k.2.2 = true ∧ d k ≠ 0
      · obtain ⟨⟨a, i, bb⟩, hk, hdk⟩ := ht
        simp only at hk
        subst hk
        set k : Fin m × Fin n × Bool := (a, i, true) with hkdef
        set d' := d - Finsupp.single k 1 with hd'
        have hdd : d = Finsupp.single k 1 + d' := by
          rw [hd', add_comm, tsub_add_cancel_of_le]
          intro j
          by_cases hj : j = k
          · subst hj; simp; omega
          · simp [Finsupp.single_apply, Ne.symm hj]
        have hsum' : d'.sum (fun _ e => e) + 1 = N := by
          rw [← hd, hdd, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
          simp [Finsupp.sum_single_index]; ring
        have hmul : monomial d (1 : ℂ) = X k * monomial d' 1 := by
          rw [hdd, X, monomial_mul, one_mul]

        have hder : ∀ j : Fin n, pderiv ((a, j, false) : Fin m × Fin n × Bool) (monomial d' (1 : ℂ)) ∈ S := by
          intro j
          rw [pderiv_monomial]
          by_cases h0 : d' (a, j, false) = 0
          · rw [h0]; simp
          · rw [show (monomial (d' - Finsupp.single (a, j, false) 1)) ((1 : ℂ) * ↑(d' (a, j, false))) =
                ((d' (a, j, false) : ℂ)) • monomial (d' - Finsupp.single (a, j, false) 1) (1 : ℂ) by
                rw [smul_monomial, smul_eq_mul, one_mul, mul_one]]
            refine S.smul_mem _ (ih _ ?_ _ rfl)
            have hle : Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 ≤ d' := by
              intro l; by_cases hl : l = (a, j, false)
              · subst hl; simp; omega
              · simp [Finsupp.single_apply, Ne.symm hl]
            have e2 : d' = Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 +
                (d' - Finsupp.single (a, j, false) 1) := by rw [add_comm, tsub_add_cancel_of_le hle]
            have : (d' - Finsupp.single (a, j, false) 1).sum (fun _ e => e) + 1 = d'.sum (fun _ e => e) := by
              conv_rhs => rw [e2]
              rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
              simp [Finsupp.sum_single_index]; ring
            omega
        choose R hR using hder
        refine ⟨∑ j, MvPolynomial.C ((c : ℂ)⁻¹) *
          MvPolynomial.X (if ε a then ((false, i, j) : Bool × Fin n × Fin n) else (true, i, j)) * R j, fun y => ?_⟩
        rw [hmul, hW m n ε c (s * c) hc _ (herm_isHermitian y)]
        simp_rw [hR]
        simp only [evUV, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [amat_inv_apply ε hc.ne' s (herm_isHermitian y), mm_inv]
        by_cases h : ε a = true <;> simp [h] <;> ring
      · push_neg at ht
        by_cases hd0 : d = 0
        · subst hd0
          exact ⟨1, fun y => by simp [evUV]⟩
        · refine ⟨0, fun y => ?_⟩
          rw [hR m n ε c (s * c) hc _ (herm_isHermitian y) d (fun k hk => ht k hk) hd0]
          simp [evUV]
  intro P
  have hP : P ∈ S := by
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one]]
    exact S.smul_mem _ (hmono _ d rfl)
  exact hP

theorem gauss_of (hI : IntegP) (hW : Wick) (hR : Rot) (hB : Base) : Gauss := by
  intro m n ε c t hc _ P
  have e : (t / c) * c = t := by field_simp
  obtain ⟨R, hR⟩ := key hI hW hR ε hc (t / c) P
  refine ⟨MvPolynomial.C (((Real.pi : ℂ) / c) ^ (n * m)) * R, fun y => ?_⟩
  have hy := hR y
  rw [e] at hy
  have hA : ∀ a, (Real.pi : ℂ) ^ n / (Amat ε c t (herm y) a).det =
      ((Real.pi : ℂ) / c) ^ n * (if ε a then uM ((t / c : ℝ) : ℂ) y else vM ((t / c : ℝ) : ℂ) y).det := by
    intro a
    have := GM.amat_det ε hc.ne' (t / c) (GM.herm_isHermitian y) a
    rw [e, mm_inv] at this
    exact this
  rw [hy, hB m n ε c t hc _ (GM.herm_isHermitian y)]
  simp_rw [hA]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [apply_ite Matrix.det]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  unfold cls
  simp only [neg_zero, Complex.cpow_zero, one_mul, evUV, map_mul, MvPolynomial.eval_C]
  rw [← pow_mul, mul_comm n m]
  have hf : (Finset.univ.filter fun a => ¬ ε a = true) = Finset.univ.filter fun a => ε a = false := by
    ext a; simp
  rw [hf]
  ring

end PositivityTheory.Rg.Sw.WR.G
