import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.GaussJetBounds.FinalB

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

namespace GramFrameCompositionTwoFacts

theorem negY_two {K : Type} [Field K] (W : WeierstrassCurve K) (x0 y0 : K)
    (h : 2 * y0 + W.a₁ * x0 + W.a₃ = 0) : W.toAffine.negY x0 y0 = y0 := by
  rw [WeierstrassCurve.Affine.negY]
  linear_combination -h

section Even

variable {K : Type} [Field K] [CharZero K]

theorem odd_coeff_of_rescale {f : PowerSeries K} (h : PowerSeries.rescale (-1 : K) f = f) (n : ℕ)
    (hn : Odd n) : PowerSeries.coeff n f = 0 := by
  have h1 := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_rescale, hn.neg_one_pow] at h1
  have h2 : (2 : K) * PowerSeries.coeff n f = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

theorem rescale_of_odd_coeff {f : PowerSeries K} (h : ∀ n : ℕ, Odd n → PowerSeries.coeff n f = 0) :
    PowerSeries.rescale (-1 : K) f = f := by
  ext n
  rw [PowerSeries.coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, one_mul]
  · rw [h n hn, mul_zero]

theorem odd_coeff_lam {e : PowerSeries K} (h : ∀ n : ℕ, Odd n → PowerSeries.coeff n e = 0) (s2 : K)
    (n : ℕ) (hn : Odd n) : PowerSeries.coeff n (lam e s2) = 0 := by
  have h2 : n ≠ 2 := by
    rintro rfl
    exact absurd hn (by decide)
  rw [lam, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg h2, mul_zero, add_zero,
    dblInt, PowerSeries.coeff_mk]
  split_ifs with h1
  · rfl
  · have h3 : Odd (n - 2) := by
      obtain ⟨k, hk⟩ := hn
      refine ⟨k - 1, ?_⟩
      omega
    rw [h _ h3, zero_div]

theorem rescale_wTr (W : WeierstrassCurve K) (x0 y0 : K) (hE : W.toAffine.Equation x0 y0)
    (h2 : 2 * y0 + W.a₁ * x0 + W.a₃ = 0) :
    PowerSeries.rescale (-1 : K) (wTr W x0 y0) = wTr W x0 y0 := by
  have he : PowerSeries.HasSubst (expSer W) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.L2.Th1.A.expSpec K W).1
  have hi : PowerSeries.HasSubst (Formalism.L2.Th1.A.iSer W) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.L2.Th1.A.iSerSpec K W).1
  have hX : ((-1 : K) • (PowerSeries.X : PowerSeries K)) = -PowerSeries.X := by
    rw [neg_smul, one_smul]
  unfold wTr
  rw [map_add, rescale_C_eq, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply he (PowerSeries.HasSubst.smul_X' (-1 : K)), hX,
    (Formalism.L2.Th1.A.logNeg K W).2, ← PowerSeries.subst_comp_subst_apply hi he,
    Formalism.L2.Th1.A.plusNeg K W x0 y0 hE, negY_two W x0 y0 h2]

end Even

section abelian₂

variable {K : Type} [Field K] [CharZero K]

theorem fact_coeff_lam (e : PowerSeries K) (s2 : K) (n : ℕ) :
    (((n + 2).factorial : ℕ) : K) * PowerSeries.coeff (n + 2) (lam e s2) =
      ((n.factorial : ℕ) : K) * PowerSeries.coeff n e + if n = 0 then s2 else 0 := by
  have h1 : ((n : K) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  have h2 : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h3 : ¬ (n + 2 < 2) := by omega
  rw [lam, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, dblInt, PowerSeries.coeff_mk,
    if_neg h3, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ]
  by_cases h0 : n = 0
  · subst h0
    simp
    field_simp
    ring
  · have h4 : n + 2 ≠ 2 := by omega
    have h5 : ((n : K) + 2 - 1) = (n : K) + 1 := by ring
    rw [if_neg h0, if_neg h4]
    push_cast
    rw [h5]
    field_simp
    ring

theorem coeff_zero_lam (e : PowerSeries K) (s2 : K) : PowerSeries.coeff 0 (lam e s2) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lam]

theorem coeff_one_lam (e : PowerSeries K) (s2 : K) : PowerSeries.coeff 1 (lam e s2) = 0 := by
  have h := constantCoeff_derivative_lam e s2
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative] at h
  simpa using h

theorem jetsIn1_lam {R : Subring K} (W : WeierstrassCurve K) (hW : CoeffIn R W) (x0 y0 s2 : K)
    (hE : W.toAffine.Equation x0 y0) (hx : x0 ∈ R) (hy : y0 ∈ R) (hs : x0 + W.b₂ / 12 + s2 ∈ R) :
    JetsIn1 R (lam (wTr W x0 y0) s2) := by
  obtain ⟨w1, w2, w3, w4, w6⟩ := hW
  have hint : ∀ n, PowerSeries.coeff n (xPlus W x0 y0) ∈ R := fun n =>
    ((Formalism.L2.Th1.A.coeffMem K W R w1 w2 w3 w4 w6).2.2.2.2.2.2.2.2.2.2 x0 hx y0 hy n).1
  have hj := (Formalism.L2.Th1.A.jetMem K W R w1 w2 w3 w4 w6).2.1 (xPlus W x0 y0) hint
  intro n
  match n with
  | 0 => rw [coeff_zero_lam, mul_zero]; exact R.zero_mem
  | 1 => rw [coeff_one_lam, mul_zero]; exact R.zero_mem
  | 2 =>
    have h := fact_coeff_lam (wTr W x0 y0) s2 0
    rw [zero_add] at h
    rw [h, if_pos rfl, Nat.factorial_zero, Nat.cast_one, one_mul, wTr, map_add,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      JetSubstitutionLemmas.cc_subst1 (Formalism.L2.Th1.A.expSpec K W).1, (Formalism.L2.Th1.A.plusFlow K W x0 y0 hE).2.1,
      PowerSeries.constantCoeff_C]
    exact hs
  | k + 3 =>
    have h := fact_coeff_lam (wTr W x0 y0) s2 (k + 1)
    rw [h, if_neg (Nat.succ_ne_zero k), add_zero, wTr, map_add, PowerSeries.coeff_C,
      if_neg (Nat.succ_ne_zero k), add_zero]
    exact hj (k + 1)

end abelian₂

section Hom

variable {K : Type} [Field K]

theorem mvSubst_subst {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ K} (hg : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) = PowerSeries.subst (MvPowerSeries.subst a g) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const ha]

theorem cc_zPt {n : Type} {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n) :
    MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) linv h0

theorem hasSubst_zPt {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries.HasSubst (fun i : n =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_zPt h0 i

def toZHom {n : Type} [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries n K →ₐ[K] MvPowerSeries n K :=
  MvPowerSeries.substAlgHom (hasSubst_zPt h0)

theorem toZHom_apply {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : MvPowerSeries n K) :
    toZHom h0 f = toZ linv f :=
  MvPowerSeries.substAlgHom_apply _ f

theorem toZ_subst_X {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : PowerSeries K) (i : n) :
    toZ linv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) f) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) (PowerSeries.subst linv f) := by
  unfold toZ
  rw [mvSubst_subst (hasSubst_zPt h0) (MvPowerSeries.constantCoeff_X i),
    MvPowerSeries.subst_X (hasSubst_zPt h0),
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]

theorem toZ_phSum {n : Type} [Fintype n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (c : n → K) (ph : PowerSeries K) :
    toZ linv (phSum c ph) = phSum c (PowerSeries.subst linv ph) := by
  unfold phSum
  rw [← toZHom_apply h0, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, toZHom_apply, toZ_subst_X h0]

theorem cc_phSum {n : Type} [Fintype n] (c : n → K) {ph : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ph = 0) : MvPowerSeries.constantCoeff (phSum c ph) = 0 := by
  unfold phSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul,
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) ph h0, mul_zero]

theorem jetsIn_phSum [CharZero K] {R : Subring K} {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ i, c i ∈ R) {f : PowerSeries K} (hf : JetsIn1 R f) :
    JetsIn R (phSum c f) := by
  unfold phSum
  refine jetsIn_sum _ _ fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul]
  exact jetsIn_mul (jetsIn_C (hc i))
    (jetsIn_subst_one hf (MvPowerSeries.constantCoeff_X i) (jetsIn_X i))

theorem jetsIn_toZ [CharZero K] {R : Subring K} {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hl : IsOneUnit R (PowerSeries.derivative K l)) {n : Type} [Fintype n]
    {G : MvPowerSeries n K} (hG : IntMv R G) : JetsIn R (toZ linv G) :=
  IntMvZ_of (JetsSubst_of jets_ring_holds jets_div_pow_holds) integral_jets_holds jets_subst_one_holds
    jets_ring_holds K R l linv h hl n G hG

theorem toZ_mvExp [CharZero K] {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) {f : MvPowerSeries n K}
    (hf : MvPowerSeries.constantCoeff f = 0) : toZ linv (mvExp f) = mvExp (toZ linv f) :=
  mvSubst_mvExp hf (hasSubst_zPt h0)

theorem subst_linv_subst_l {l linv : PowerSeries K} (h : IsLogPair l linv) (f : PowerSeries K) :
    PowerSeries.subst linv (PowerSeries.subst l f) = f := by
  rw [PowerSeries.subst_comp_subst_apply (JetSubstitutionLemmas.hs1 h.1) (JetSubstitutionLemmas.hs1 h.2.2.1), h.2.2.2.2,
    PowerSeries.X_subst]

end Hom

theorem wpShift_eq {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K)
    (hE : W.toAffine.Equation x0 y0) (h2 : 2 * y0 + W.a₁ * x0 + W.a₃ = 0) :
    wpShift (wpReg W) (x0 + W.b₂ / 12) =
      pExp (2 • lam (wpReg W) s2 + 2 • (-(lam (wTr W x0 y0) s2))) := by
  have hD := curve_second_log_derivative K W x0 y0 hE
  rw [negY_two W x0 y0 h2] at hD
  set L : PowerSeries K := 2 • lam (wpReg W) s2 + 2 • (-(lam (wTr W x0 y0) s2)) with hL
  have cL : PowerSeries.constantCoeff L = 0 := by
    rw [hL, map_add, map_nsmul, map_nsmul, map_neg, constantCoeff_lam, constantCoeff_lam]
    simp
  have cL' : PowerSeries.constantCoeff (PowerSeries.derivative K L) = 0 := by
    rw [hL, map_add, map_nsmul, map_nsmul, map_neg, map_add, map_nsmul, map_nsmul, map_neg,
      constantCoeff_derivative_lam, constantCoeff_derivative_lam]
    simp
  have dL : PowerSeries.derivative K (PowerSeries.derivative K L) =
      2 * wpReg W - wTr W x0 y0 - wTr W x0 y0 := by
    rw [hL]
    simp only [map_add, map_nsmul, map_neg, derivative2_lam]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hP := hasSecondLogDeriv_powerSeriesExp L cL
  rw [dL] at hP
  refine hasSecondLogDeriv_left_unique ?_ (constantCoeff_pExp mvExpLaws L cL) ?_ hD hP
  · simp [wpShift]
  · rw [derivative_pExp L cL, map_mul, cL', mul_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative, wpShift, map_add, PowerSeries.coeff_X_pow_mul']
    simp [PowerSeries.coeff_one]

end GramFrameCompositionTwoFacts

open GramFrameCompositionTwoFacts

theorem theta_zero_square_holds : ThetaZeroSquare := by
  intro K _ _ W x0 y0 s2 hE h2
  have c1 : PowerSeries.constantCoeff (lam (wpReg W) s2) = 0 := constantCoeff_lam _ _
  have c2 : PowerSeries.constantCoeff (-(lam (wTr W x0 y0) s2)) = 0 := by
    rw [map_neg, constantCoeff_lam, neg_zero]
  have e1 : PowerSeries.constantCoeff (2 • lam (wpReg W) s2) = 0 := by
    rw [map_nsmul, c1, smul_zero]
  have e2 : PowerSeries.constantCoeff (2 • (-(lam (wTr W x0 y0) s2))) = 0 := by
    rw [map_nsmul, c2, smul_zero]
  rw [wpShift_eq W x0 y0 s2 hE h2, pExp_add mvExpLaws _ _ e1 e2, pExp_nsmul mvExpLaws _ c1,
    pExp_nsmul mvExpLaws _ c2]
  have h := pExp_mul_neg mvExpLaws (lam (wpReg W) s2) c1
  change PowerSeries.X ^ 2 * pExp (-(lam (wTr W x0 y0) s2)) ^ 2 =
    (PowerSeries.X * pExp (-(lam (wpReg W) s2))) ^ 2 *
      (pExp (lam (wpReg W) s2) ^ 2 * pExp (-(lam (wTr W x0 y0) s2)) ^ 2)
  linear_combination (-(PowerSeries.X ^ 2 * pExp (-(lam (wTr W x0 y0) s2)) ^ 2 *
    (pExp (lam (wpReg W) s2) * pExp (-(lam (wpReg W) s2)) + 1))) * h

theorem theta_zero_even_holds : ThetaZeroEven := by
  intro K _ _ W x0 y0 s2 hE h2
  have c2 : PowerSeries.constantCoeff (-(lam (wTr W x0 y0) s2)) = 0 := by
    rw [map_neg, constantCoeff_lam, neg_zero]
  refine ⟨constantCoeff_pExp mvExpLaws _ c2, ?_⟩
  have hw := odd_coeff_of_rescale (rescale_wTr W x0 y0 hE h2)
  have hl : PowerSeries.rescale (-1 : K) (lam (wTr W x0 y0) s2) = lam (wTr W x0 y0) s2 :=
    rescale_of_odd_coeff (odd_coeff_lam hw s2)
  refine odd_coeff_of_rescale ?_
  change PowerSeries.rescale (-1 : K) (pExp (-(lam (wTr W x0 y0) s2))) = pExp _
  rw [rescale_pExp _ _ c2, map_neg, hl]

theorem s2_integral_holds : ShiftedSigmaConstantIntegralOfIsogenySum := by
  intro K _ _ _ s2 al albar b ι _ xP hN hu hx hb hs
  have key : al * (al - albar) * (s2 + b / 12) = ∑ P, xP P + (al ^ 2 - 1) * (b / 12) := by
    rw [mul_add, hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination (-(b / 12)) * hN
  have e : ‖s2 + b / 12‖ = ‖al * (al - albar) * (s2 + b / 12)‖ := by
    rw [norm_mul (al * (al - albar)), hu, one_mul]
  rw [e, key]
  exact (unitBall K).add_mem (Subring.sum_mem _ fun P _ => hx P) hb

theorem theta_zero_jets_two_holds : ThetaZeroJetsTwo := by
  intro K _ _ _ W hW x0 y0 s2 hE h2 hx hy hs
  obtain ⟨hlp, -, -, -, hl1⟩ := curveFrame K (unitBall K) W hW
  have hΛ : JetsIn1 (unitBall K) (lam (wTr W x0 y0) s2) := jetsIn1_lam W hW x0 y0 s2 hE hx hy hs
  have cΛ : PowerSeries.constantCoeff (lam (wTr W x0 y0) s2) = 0 := constantCoeff_lam _ _
  have cph : PowerSeries.constantCoeff (phT W x0 y0 s2) = 0 := by
    unfold phT
    rw [JetSubstitutionLemmas.cc_subst1 hlp.1, cΛ]
  have p1 : ∀ i : ℕ, jet (logSer W) (phT W x0 y0 s2) i ∈ unitBall K := by
    intro i
    rw [jetAdditive K _ _ _ hlp i, phT, subst_linv_subst_l hlp]
    exact hΛ i
  have eq : PowerSeries.subst (logSer W) (th0 W x0 y0 s2) =
      (mvExp (-(phT W x0 y0 s2)) : PowerSeries K) := by
    unfold th0 phT
    rw [mvExpSubst K Unit (-(lam (wTr W x0 y0) s2)) (logSer W) (by rw [map_neg, cΛ, neg_zero]) hlp.1]
    congr 1
    rw [← sub_eq_zero, sub_neg_eq_add, ← PowerSeries.subst_add (JetSubstitutionLemmas.hs1 hlp.1), neg_add_cancel,
      ← PowerSeries.coe_substAlgHom (JetSubstitutionLemmas.hs1 hlp.1), map_zero]
  have p3 : ∀ i : ℕ, jet (logSer W) (PowerSeries.subst (logSer W) (th0 W x0 y0 s2)) i ∈
      unitBall K := by
    intro i
    rw [eq]
    exact jetExp K (unitBall K) _ _ _ hlp cph (fun i _ => p1 i) i
  have p2 := (jets_of_dist_jets_holds K (unitBall K) _ _ _ hlp).1 p3
  rw [subst_linv_subst_l hlp] at p2
  exact ⟨fun i _ => p1 i, p2, p3⟩

theorem Th0JetsCurve_of (h1 : ShiftedSigmaConstantIntegralOfIsogenySum) (h2 : ThetaZeroJetsTwo) : ThetaZeroJetsCurve := by
  intro K _ _ _ W hW s2 al albar ι _ neg xP yP _ hxP _ hN hu hb hs x0 y0 hE hT hx hy
  have a1 : ‖s2 + W.b₂ / 12‖ ≤ 1 := h1 K s2 al albar W.b₂ ι xP hN hu hxP hb hs
  have a2 : ‖x0 + W.b₂ / 12 + s2‖ ≤ 1 := by
    have e : x0 + W.b₂ / 12 + s2 = x0 + (s2 + W.b₂ / 12) := by ring
    rw [e]
    exact (unitBall K).add_mem hx a1
  obtain ⟨q1, q2, -⟩ := h2 K W hW x0 y0 s2 hE hT hx hy a2
  exact ⟨q2, q1⟩

theorem theta_zero_jets_curve_holds : ThetaZeroJetsCurve := Th0JetsCurve_of s2_integral_holds theta_zero_jets_two_holds

theorem kernel_two_holds : KernelTwo := by
  intro K _ _ _ l linv ph h hl hph hj n _ c hc G hG
  have hv : PowerSeries.constantCoeff linv = 0 := h.2.2.1
  have j0 : JetsIn1 (unitBall K) (PowerSeries.subst linv ph) := by
    refine (jets_of_dist_jets_holds K (unitBall K) l linv ph h).1 fun i => ?_
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have : jet l ph 0 = 0 := hph
      rw [this]
      exact (unitBall K).zero_mem
    · exact hj i hi
  have cz : PowerSeries.constantCoeff (PowerSeries.subst linv ph) = 0 := by
    rw [JetSubstitutionLemmas.cc_subst1 hv, hph]
  have c1 : MvPowerSeries.constantCoeff (-(phSum c ph)) = 0 := by
    rw [map_neg, cc_phSum c hph, neg_zero]
  have c3 : MvPowerSeries.constantCoeff (-(phSum c (PowerSeries.subst linv ph))) = 0 := by
    rw [map_neg, cc_phSum c cz, neg_zero]
  have e : toZ linv (-(phSum c ph)) = -(phSum c (PowerSeries.subst linv ph)) := by
    rw [← toZHom_apply hv, map_neg, toZHom_apply, toZ_phSum hv]
  have key : JetsIntegral (toZ linv (mvExp (-(phSum c ph)) * G)) := by
    rw [← toZHom_apply hv, map_mul, toZHom_apply, toZHom_apply, toZ_mvExp hv c1, e]
    exact jetsIn_mul (R := unitBall K) (jetsIn_mvExp c3 (jetsIn_neg (jetsIn_phSum hc j0)))
      (jetsIn_toZ h hl hG)
  exact ⟨key, fun P hP => Formalism.DworkPowerSeriesWeights.intOp K n _ key P hP⟩

theorem CurveKernelTwo_of (h : ThetaZeroJetsCurve) (hK : KernelTwo) : CurveKernelTwo := by
  intro K _ _ _ W hW s2 al albar ι _ neg xP yP hEnd hxP hyP hN hu hb hs x0 y0 hE hT hx hy n _ c hc
    G hG P hP
  obtain ⟨hlp, -, -, -, hl1⟩ := curveFrame K (unitBall K) W hW
  have hj := (h K W hW s2 al albar ι neg xP yP hEnd hxP hyP hN hu hb hs x0 y0 hE hT hx hy).2
  have cph : PowerSeries.constantCoeff (phT W x0 y0 s2) = 0 := by
    unfold phT
    rw [JetSubstitutionLemmas.cc_subst1 hlp.1, constantCoeff_lam]
  exact (hK K _ _ _ hlp hl1 cph hj n c hc G hG).2 P hP

theorem curve_kernel_two_holds : CurveKernelTwo :=
  CurveKernelTwo_of theta_zero_jets_curve_holds kernel_two_holds

end Formalism.L2.Th1.G
