import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IntBinomScalar
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.ChordSecondLogDeriv

noncomputable section
open scoped BigOperators
open PowerSeries

namespace Formalism.L2.Th1.C

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [CharZero K]

def pExp (f : PowerSeries K) : PowerSeries K := mvExp f

theorem pExp_zero (hE : MvExpLaws) : pExp (0 : PowerSeries K) = 1 := (hE K Unit).1

theorem constantCoeff_pExp (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    constantCoeff (pExp f) = 1 := (hE K Unit).2.1 f hf

theorem pExp_add (hE : MvExpLaws) (f g : PowerSeries K) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : pExp (f + g) = pExp f * pExp g := (hE K Unit).2.2.1 f g hf hg

theorem pExp_mul_neg (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    pExp f * pExp (-f) = 1 := by
  rw [← pExp_add hE f (-f) hf (by rw [map_neg, hf, neg_zero]), add_neg_cancel, pExp_zero hE]

theorem pExp_nsmul (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) (k : ℕ) :
    pExp (k • f) = pExp f ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, pExp_zero hE]
  | succ k ih =>
    have hk : constantCoeff (k • f) = 0 := by rw [map_nsmul, hf, smul_zero]
    rw [succ_nsmul, pExp_add hE _ _ hk hf, ih, pow_succ]

theorem rescale_pExp (a : K) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    rescale a (pExp f) = pExp (rescale a f) := by
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  have hX : PowerSeries.HasSubst (a • PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  show rescale a (PowerSeries.subst f (PowerSeries.exp K)) =
    PowerSeries.subst (rescale a f) (PowerSeries.exp K)
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hs hX, ← PowerSeries.rescale_eq_subst]

theorem derivative_pExp (f : PowerSeries K) (hf : constantCoeff f = 0) :
    derivative K (pExp f) = pExp f * derivative K f := by
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  show derivative K (PowerSeries.subst f (PowerSeries.exp K)) =
    PowerSeries.subst f (PowerSeries.exp K) * derivative K f
  rw [PowerSeries.derivative_subst hs, PowerSeries.derivative_exp]

theorem hasSecondLogDeriv_one : HasSecondLogDeriv (1 : PowerSeries K) 0 := by
  simp [HasSecondLogDeriv]

theorem hasSecondLogDeriv_mul {f h g₁ g₂ : PowerSeries K} (h1 : HasSecondLogDeriv f g₁) (h2 : HasSecondLogDeriv h g₂) :
    HasSecondLogDeriv (f * h) (g₁ + g₂) := by
  unfold HasSecondLogDeriv at *
  have e1 : derivative K (f * h) = derivative K f * h + f * derivative K h := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  have e2 : derivative K (derivative K f * h + f * derivative K h) =
      derivative K (derivative K f) * h + 2 * (derivative K f * derivative K h) +
        f * derivative K (derivative K h) := by
    rw [map_add, Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  rw [e1, e2]
  linear_combination h ^ 2 * h1 + f ^ 2 * h2

theorem hasSecondLogDeriv_prod {ι : Type} (s : Finset ι) (f g : ι → PowerSeries K)
    (h : ∀ i ∈ s, HasSecondLogDeriv (f i) (g i)) : HasSecondLogDeriv (∏ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    exact hasSecondLogDeriv_one
  · intro a s ha ih hh
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact hasSecondLogDeriv_mul (hh a (Finset.mem_insert_self a s))
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

theorem hasSecondLogDeriv_powerSeriesExp (L : PowerSeries K) (hL : constantCoeff L = 0) :
    HasSecondLogDeriv (pExp L) (derivative K (derivative K L)) := by
  unfold HasSecondLogDeriv
  have h1 := derivative_pExp L hL
  rw [h1, Derivation.leibniz, h1]
  simp only [smul_eq_mul]
  ring

theorem hasSecondLogDeriv_right_unique {f g g' : PowerSeries K} (hf : f ≠ 0) (h1 : HasSecondLogDeriv f g)
    (h2 : HasSecondLogDeriv f g') : g = g' := by
  unfold HasSecondLogDeriv at h1 h2
  exact mul_right_cancel₀ (pow_ne_zero 2 hf) (h1.symm.trans h2)

theorem eq_C_mul_of_wronskian {a b : PowerSeries K} (hb : constantCoeff b = 1)
    (h : b * derivative K a = a * derivative K b) : a = C (constantCoeff a) * b := by
  have hb0 : constantCoeff b ≠ 0 := by rw [hb]; exact one_ne_zero
  have hinv : b * b⁻¹ = 1 := PowerSeries.mul_inv_cancel b hb0
  have hq : derivative K (a * b⁻¹) = derivative K (C (constantCoeff a)) := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv', PowerSeries.derivative_C]
    simp only [smul_eq_mul]
    linear_combination (-(b⁻¹ * derivative K a)) * hinv + (b⁻¹ ^ 2) * h
  have hq2 : a * b⁻¹ = C (constantCoeff a) :=
    PowerSeries.derivative.ext hq (by
      rw [map_mul, PowerSeries.constantCoeff_inv, hb, inv_one, mul_one, PowerSeries.constantCoeff_C])
  calc a = a * b⁻¹ * b := by rw [mul_assoc, PowerSeries.inv_mul_cancel b hb0, mul_one]
    _ = C (constantCoeff a) * b := by rw [hq2]

theorem hasSecondLogDeriv_left_unique {f h g : PowerSeries K} (hf : constantCoeff f = 1)
    (hh : constantCoeff h = 1)
    (h1 : constantCoeff (derivative K f) = constantCoeff (derivative K h))
    (hfg : HasSecondLogDeriv f g) (hhg : HasSecondLogDeriv h g) : f = h := by
  unfold HasSecondLogDeriv at hfg hhg
  have hf0 : constantCoeff f ≠ 0 := by rw [hf]; exact one_ne_zero
  have hh0 : constantCoeff h ≠ 0 := by rw [hh]; exact one_ne_zero
  have if1 := PowerSeries.mul_inv_cancel f hf0
  have ih1 := PowerSeries.mul_inv_cancel h hh0
  have dA : derivative K (derivative K f * f⁻¹) = g := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv']
    simp only [smul_eq_mul]
    linear_combination f⁻¹ ^ 2 * hfg +
      (g * (f * f⁻¹ + 1) - derivative K (derivative K f) * f⁻¹) * if1
  have dB : derivative K (derivative K h * h⁻¹) = g := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv']
    simp only [smul_eq_mul]
    linear_combination h⁻¹ ^ 2 * hhg +
      (g * (h * h⁻¹ + 1) - derivative K (derivative K h) * h⁻¹) * ih1
  have hA : derivative K f * f⁻¹ = derivative K h * h⁻¹ := by
    apply PowerSeries.derivative.ext (by rw [dA, dB])
    rw [map_mul, map_mul, PowerSeries.constantCoeff_inv, PowerSeries.constantCoeff_inv, hf, hh, h1]
  have hw : h * derivative K f = f * derivative K h := by
    linear_combination (f * h) * hA + (-(h * derivative K f)) * if1 + (f * derivative K h) * ih1
  have hfh := eq_C_mul_of_wronskian hh hw
  rw [hfh, hf, map_one, one_mul]

end SlopeTestRemainingChoices

section Calc

variable {K : Type} [Field K] [CharZero K]

theorem derivative_rescale (a : K) (f : PowerSeries K) :
    derivative K (rescale a f) = a • rescale a (derivative K f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem rescale_C_eq (a b : K) : rescale a (C b : PowerSeries K) = C b := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hn <;> simp [hn]

theorem constantCoeff_rescale_eq (a : K) (f : PowerSeries K) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, pow_zero, one_mul]

theorem derivative2_dblInt (e : PowerSeries K) :
    derivative K (derivative K (dblInt e)) = e := by
  ext n
  simp only [dblInt, PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  rw [if_neg (show ¬ (n + 1 + 1 < 2) by omega), show n + 1 + 1 - 2 = n by omega]
  push_cast
  rw [show (n : K) + 1 + 1 - 1 = n + 1 by ring]
  have h1 : (n : K) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have h2 : (n : K) + 1 + 1 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
  field_simp <;> ring

theorem derivative2_lam (e : PowerSeries K) (s2 : K) :
    derivative K (derivative K (lam e s2)) = e + C s2 := by
  unfold lam
  rw [map_add, map_add, derivative2_dblInt]
  congr 1
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]
  rcases n with _ | n
  · norm_num
  · simp

theorem constantCoeff_lam (e : PowerSeries K) (s2 : K) : constantCoeff (lam e s2) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [lam, dblInt, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

theorem constantCoeff_derivative_lam (e : PowerSeries K) (s2 : K) :
    constantCoeff (derivative K (lam e s2)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp [lam, dblInt, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

theorem prod_wpShift_form {ι : Type} (s : Finset ι) (e : PowerSeries K) (c : ι → K) :
    ∃ r : PowerSeries K, ∏ P ∈ s, wpShift e (c P) = 1 + X ^ 2 * r := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro a s ha ⟨r, hr⟩
  refine ⟨(e - C (c a)) + r + X ^ 2 * (e - C (c a)) * r, ?_⟩
  rw [Finset.prod_insert ha, hr, wpShift]
  ring

end Calc

section Main

theorem isogenyReduce_of (hE : MvExpLaws) : IsogenyReduce := by
  intro K _ _ e s2 ι _ c al hal
  have hL : constantCoeff (lam e s2) = 0 := constantCoeff_lam e s2
  have hR : constantCoeff (rescale al (lam e s2)) = 0 := by rw [constantCoeff_rescale_eq, hL]
  have hA1 : pExp (lam e s2) * pExp (-(lam e s2)) = 1 := pExp_mul_neg hE _ hL
  have hresc : rescale al (sgStar e s2) = C al * X * pExp (-(rescale al (lam e s2))) := by
    have h1 := rescale_pExp al (-(lam e s2)) (by rw [map_neg, hL, neg_zero])
    rw [map_neg] at h1
    show rescale al (X * pExp (-(lam e s2))) = _
    rw [map_mul, PowerSeries.rescale_X, h1]
  have e1 : (2 * ((Fintype.card ι : K) + 1)) • lam e s2 = (2 * (Fintype.card ι + 1)) • lam e s2 := by
    rw [← Nat.cast_smul_eq_nsmul K]
    norm_num
  have e2 : -((2 : K) • rescale al (lam e s2)) = 2 • (-(rescale al (lam e s2))) := by
    rw [two_smul, two_smul]
    abel
  have hT : pExp ((2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • rescale al (lam e s2)) =
      pExp (lam e s2) ^ (2 * (Fintype.card ι + 1)) * pExp (-(rescale al (lam e s2))) ^ 2 := by
    rw [sub_eq_add_neg, e1, e2,
      pExp_add hE _ _ (by rw [map_nsmul, hL, smul_zero]) (by rw [map_nsmul, map_neg, hR, neg_zero, smul_zero]),
      pExp_nsmul hE _ hL, pExp_nsmul hE _ (by rw [map_neg, hR, neg_zero])]
  have hsg : sgStar e s2 = X * pExp (-(lam e s2)) := rfl
  have hne : (C (al ^ 2) * X ^ (2 * Fintype.card ι + 2) : PowerSeries K) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ PowerSeries.X_ne_zero)
    intro h0
    apply hal
    simpa using congrArg constantCoeff h0
  unfold IsogenyFormula
  change _ ↔ pExp _ = _
  rw [hT, hresc, hsg]
  have lhs : (C al * X * pExp (-(rescale al (lam e s2)))) ^ 2 * X ^ (2 * Fintype.card ι) =
      (C (al ^ 2) * X ^ (2 * Fintype.card ι + 2)) * pExp (-(rescale al (lam e s2))) ^ 2 := by
    rw [map_pow]
    ring
  have rhs : C (al ^ 2) * (X * pExp (-(lam e s2))) ^ (2 * (Fintype.card ι + 1)) * ∏ P, wpShift e (c P) =
      (C (al ^ 2) * X ^ (2 * Fintype.card ι + 2)) *
        (pExp (-(lam e s2)) ^ (2 * (Fintype.card ι + 1)) * ∏ P, wpShift e (c P)) := by
    ring
  rw [lhs, rhs, mul_right_inj' hne]
  constructor
  · intro h
    rw [h, ← mul_assoc, ← mul_pow, hA1, one_pow, one_mul]
  · intro h
    rw [← h, ← mul_assoc, ← mul_pow, mul_comm (pExp (-(lam e s2))), hA1, one_pow, one_mul]

theorem isogenyIff_of (hE : MvExpLaws) : IsogenyIff := by
  intro K _ _ e s2 ι _ neg c w al hal hendo
  obtain ⟨hneg, hD, hend⟩ := hendo
  rw [isogenyReduce_of hE K e s2 ι c al hal]
  change pExp _ = _ ↔ _
  have hL : constantCoeff (lam e s2) = 0 := constantCoeff_lam e s2
  set Φ := (2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • rescale al (lam e s2) with hΦdef
  have hΦ : constantCoeff Φ = 0 := by
    rw [hΦdef]
    simp [PowerSeries.smul_eq_C_mul, constantCoeff_rescale_eq, hL]
  have hΦ1 : constantCoeff (derivative K Φ) = 0 := by
    rw [hΦdef]
    simp [PowerSeries.smul_eq_C_mul, derivative_rescale, Derivation.map_smul, constantCoeff_rescale_eq,
      constantCoeff_derivative_lam]
  set W := ∏ P, wpShift e (c P) with hWdef
  set g := ∑ P, (2 * e - w P - w (neg P)) with hgdef
  have hWg : HasSecondLogDeriv W g := hasSecondLogDeriv_prod _ _ _ fun P _ => hD P
  have hEg : HasSecondLogDeriv (pExp Φ) (derivative K (derivative K Φ)) := hasSecondLogDeriv_powerSeriesExp Φ hΦ
  have hsum_neg : ∑ P, w (neg P) = ∑ P, w P := Equiv.sum_comp (Function.Involutive.toPerm neg hneg) w
  have hg : g = (Fintype.card ι : PowerSeries K) * (2 * e) - 2 * ∑ P, w P := by
    rw [hgdef, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum_neg, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hend' : C al ^ 2 * rescale al e = e + ∑ P, w P - C (∑ P, c P) := by
    rw [← map_pow, hend, Finset.sum_sub_distrib, map_sum]
    ring
  have hd : derivative K (derivative K Φ) = g + C (2 * (∑ P, c P - (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2)) := by
    rw [hΦdef, map_sub, map_sub, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul,
      derivative_rescale, Derivation.map_smul, derivative_rescale, derivative2_lam, map_add, rescale_C_eq, hg]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_sub, map_add, map_pow, map_natCast, map_one, map_ofNat]
    linear_combination (-2 : PowerSeries K) * hend'
  constructor
  · intro h
    have hW0 : W ≠ 0 := by
      intro h0
      have h3 := constantCoeff_pExp hE Φ hΦ
      rw [h, h0, map_zero] at h3
      exact zero_ne_one h3
    have hEg' := hEg
    rw [h] at hEg'
    have h1 := hasSecondLogDeriv_right_unique hW0 hEg' hWg
    rw [hd] at h1
    have h2 : C (2 * (∑ P, c P - (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2)) = 0 := by
      linear_combination h1
    have h3 := congrArg constantCoeff h2
    rw [PowerSeries.constantCoeff_C, map_zero] at h3
    have h4 := (mul_eq_zero.1 h3).resolve_left two_ne_zero
    linear_combination -1 * h4
  · intro h
    have hΦg : derivative K (derivative K Φ) = g := by
      rw [hd, ← h, sub_self, mul_zero, map_zero, add_zero]
    obtain ⟨r, hr⟩ := prod_wpShift_form Finset.univ e c
    have hW1 : constantCoeff W = 1 := by
      rw [hWdef, hr]
      simp
    have hW2 : constantCoeff (derivative K W) = 0 := by
      rw [hWdef, hr, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
      simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
    have hWg' : HasSecondLogDeriv W (derivative K (derivative K Φ)) := by rw [hΦg]; exact hWg
    exact hasSecondLogDeriv_left_unique (constantCoeff_pExp hE Φ hΦ) hW1
      (by rw [derivative_pExp Φ hΦ, map_mul, hΦ1, mul_zero, hW2]) hEg hWg'

theorem isogenyIffBar_of (hE : MvExpLaws) : IsogenyIffBar := by
  intro K _ _ e s2 ι _ neg xP c0 w al albar hal hbar hendo
  rw [isogenyIff_of hE K e s2 ι neg (fun P => xP P + c0) w al hal hendo, ← hbar]
  constructor <;> intro h <;> linear_combination h

end Main

end Formalism.L2.Th1.C
