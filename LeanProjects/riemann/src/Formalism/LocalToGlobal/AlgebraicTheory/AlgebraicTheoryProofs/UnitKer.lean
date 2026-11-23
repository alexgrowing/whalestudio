import Formalism.LocalToGlobal.AlgebraicTheory.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NeZeroOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

namespace UnitKernelIntegral

open PowerSeries
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL ptOf px py GaussOne IntS)
open Formalism.L2.Th1.A (logSer expSer wpReg xS)
open Formalism.L2.Th1.C (IntPS IntMv LG Cong mvExp mulBy EndInt PhNormAt IsEndoZ)
open Formalism.L2.Th1.D (normInt)
open Formalism.L2.Th1.D.GaussNormEstimates (normZ_lt normZ_one normZ_le norm_one_of_close)
open Formalism.L2.Th1.Top.CalcPAux
open Formalism.G (unitBall)

section Int

variable {K : Type} [Field K] (R : Subring K)

theorem intPS_mul {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f * g) := by
  intro n
  rw [coeff_mul]
  exact R.sum_mem fun x _ => R.mul_mem (hf _) (hg _)

theorem intPS_C {c : K} (hc : c ∈ R) : IntPS R (C c) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact R.zero_mem

theorem prod_int [CharZero K] (v ph A : PowerSeries K) {ι : Type} [Fintype ι] (xP : ι → K) (al N : K)
    (hal : al ≠ 0) (hali : al⁻¹ ∈ R) (hv0 : constantCoeff v = 0) (hv : IntPS R v)
    (hph0 : constantCoeff ph = 0)
    (hD : Cong R (PowerSeries.subst v ph) (N • ph))
    (hU : v ^ 2 * mvExp (-((2 : K) • PowerSeries.subst v ph)) * X ^ (2 * Fintype.card ι) =
      C (al ^ 2) * X ^ (2 * (Fintype.card ι + 1)) * mvExp (-((2 * N) • ph))
        * ∏ P, (A - C (xP P) * X ^ 2)) :
    IntPS R (∏ P, (A - C (xP P) * X ^ 2)) := by
  set D : PowerSeries K := PowerSeries.subst v ph - N • ph with hDdef
  obtain ⟨hexp0, hcc1, hadd, -⟩ := Formalism.L2.Th1.C.mvExpLaws K Unit
  obtain ⟨-, hLGadd, hLGneg⟩ := Formalism.L2.Th1.C.lGSubgroup K R Unit
  have h2D : LG R (-(D + D)) := hLGneg _ (hLGadd _ _ hD hD)
  have hM0 : MvPowerSeries.constantCoeff (-((2 * N) • ph) : MvPowerSeries Unit K) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul]
    simp only [map_neg, map_mul, MvPowerSeries.constantCoeff_C, neg_eq_zero, mul_eq_zero]
    right
    exact hph0
  have e1 : -((2 : K) • PowerSeries.subst v ph) = -(D + D) + -((2 * N) • ph) := by
    rw [hDdef, mul_smul, two_smul, two_smul]
    abel
  have hsplit : mvExp (-((2 : K) • PowerSeries.subst v ph)) =
      mvExp (-(D + D)) * mvExp (-((2 * N) • ph)) := by
    rw [e1]
    exact hadd _ _ h2D.1 hM0
  set E1 : PowerSeries K := mvExp (-(D + D))
  set E2 : PowerSeries K := mvExp (-((2 * N) • ph))
  have hE2 : E2 ≠ 0 := by
    intro h0
    have := hcc1 _ hM0
    change MvPowerSeries.constantCoeff E2 = 1 at this
    rw [h0, map_zero] at this
    exact zero_ne_one this
  rw [hsplit] at hU
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  have h1 : (v ^ 2 * E1) * (E2 * X ^ (2 * Fintype.card ι)) =
      (C (al ^ 2) * X ^ 2 * ∏ P, (A - C (xP P) * X ^ 2)) * (E2 * X ^ (2 * Fintype.card ι)) := by
    linear_combination hU
  have h2 := mul_right_cancel₀ (mul_ne_zero hE2 (pow_ne_zero _ hX)) h1
  obtain ⟨h, rfl⟩ := X_dvd_iff.2 hv0
  have h3 : X ^ 2 * (h ^ 2 * E1) = X ^ 2 * (C (al ^ 2) * ∏ P, (A - C (xP P) * X ^ 2)) := by
    linear_combination h2
  have h4 := mul_left_cancel₀ (pow_ne_zero 2 hX) h3
  have h5 : ∏ P, (A - C (xP P) * X ^ 2) = C (al⁻¹ ^ 2) * (h ^ 2 * E1) := by
    rw [h4, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hal, one_pow, map_one, one_mul]
  rw [h5]
  have hh : IntPS R h := by
    intro n
    have := hv (n + 1)
    rwa [coeff_succ_X_mul] at this
  have hE1 : IntPS R E1 := fun n => h2D.2 _
  exact intPS_mul R (intPS_C R (R.pow_mem hali 2)) (intPS_mul R (by rw [pow_two]; exact intPS_mul R hh hh) hE1)

end Int

section Gauss

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rw [norm_neg]; exact hy))

theorem gaussOne_one : GaussOne (1 : PowerSeries K) := by
  refine ⟨fun n => ?_, 0, by simp⟩
  rw [coeff_one]
  split_ifs <;> simp

theorem coeff_factor (A : PowerSeries K) (c : K) (n : ℕ) :
    coeff n (A - C c * X ^ 2) = coeff n A - if n = 2 then c else 0 := by
  rw [map_sub, coeff_C_mul_X_pow]

theorem gauss_roots {ι : Type} [Fintype ι] (A : PowerSeries K) (hA0 : constantCoeff A = 1)
    (hA : ∀ n, ‖coeff n A‖ ≤ 1) (c : ι → K)
    (hF : ∀ n, ‖coeff n (∏ P, (A - C (c P) * X ^ 2))‖ ≤ 1) : ∀ P, ‖c P‖ ≤ 1 := by
  classical
  set d : ι → K := fun P => if ‖c P‖ ≤ 1 then 1 else c P with hd
  have hd1 : ∀ P, 1 ≤ ‖d P‖ := by
    intro P
    simp only [hd]
    split_ifs with h
    · simp
    · exact (not_le.1 h).le
  have hd0 : ∀ P, d P ≠ 0 := by
    intro P h
    have := hd1 P
    rw [h, norm_zero] at this
    linarith
  set g : ι → PowerSeries K := fun P => C (d P)⁻¹ * (A - C (c P) * X ^ 2) with hg
  have hgc : ∀ P n, coeff n (g P) = (d P)⁻¹ * (coeff n A - if n = 2 then c P else 0) := by
    intro P n
    simp only [hg]
    rw [coeff_C_mul, coeff_factor]
  have hG1 : ∀ P, GaussOne (g P) := by
    intro P
    by_cases h : ‖c P‖ ≤ 1
    · have hdP : d P = 1 := by simp only [hd]; rw [if_pos h]
      refine ⟨fun n => ?_, 0, ?_⟩
      · rw [hgc, hdP, inv_one, one_mul]
        apply norm_sub_le_one (hA n)
        split_ifs
        · exact h
        · simp
      · rw [hgc, hdP, inv_one, one_mul, if_neg (by norm_num), sub_zero, coeff_zero_eq_constantCoeff_apply, hA0,
          norm_one]
    · have hdP : d P = c P := by simp only [hd]; rw [if_neg h]
      have hc1 : 1 < ‖c P‖ := not_le.1 h
      have hc0 : c P ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hc1
        linarith
      have hci : ‖(c P)⁻¹‖ < 1 := by
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hc1
      have hsmall : ∀ n, ‖(c P)⁻¹ * coeff n A‖ < 1 := by
        intro n
        rw [norm_mul]
        calc ‖(c P)⁻¹‖ * ‖coeff n A‖ ≤ ‖(c P)⁻¹‖ * 1 :=
              mul_le_mul_of_nonneg_left (hA n) (norm_nonneg _)
          _ < 1 := by rw [mul_one]; exact hci
      have e : ∀ n, coeff n (g P) = (c P)⁻¹ * coeff n A - if n = 2 then 1 else 0 := by
        intro n
        rw [hgc, hdP, mul_sub]
        split_ifs
        · rw [inv_mul_cancel₀ hc0]
        · rw [mul_zero]
      refine ⟨fun n => ?_, 2, ?_⟩
      · rw [e]
        apply norm_sub_le_one (hsmall n).le
        split_ifs <;> simp
      · rw [e, if_pos rfl]
        apply norm_one_of_close (b := -1)
        · rw [sub_neg_eq_add, sub_add_cancel]
          exact hsmall 2
        · simp
  have hfac : ∏ P, (A - C (c P) * X ^ 2) = C (∏ P, d P) * ∏ P, g P := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    simp only [hg]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hd0 P), map_one, one_mul]
  have hG : GaussOne (∏ P, g P) :=
    Finset.prod_induction _ GaussOne (fun f g hf hg => Formalism.L2.Th1.E.gaussMul K f g hf hg) gaussOne_one
      (fun P _ => hG1 P)
  obtain ⟨n, hn⟩ := hG.2
  have hc := hF n
  rw [hfac, coeff_C_mul, norm_mul, hn, mul_one, norm_prod] at hc
  intro P
  by_contra hP
  have hdP : d P = c P := by simp only [hd]; rw [if_neg hP]
  have hrest : (1 : ℝ) ≤ ∏ Q ∈ Finset.univ.erase P, ‖d Q‖ := by
    calc (1 : ℝ) = ∏ Q ∈ Finset.univ.erase P, (1 : ℝ) := by rw [Finset.prod_const_one]
      _ ≤ ∏ Q ∈ Finset.univ.erase P, ‖d Q‖ :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun Q _ => hd1 Q)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P), hdP] at hc
  have : ‖c P‖ * 1 ≤ ‖c P‖ * ∏ Q ∈ Finset.univ.erase P, ‖d Q‖ :=
    mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
  linarith [not_le.1 hP]

end Gauss

section Three

variable {p : ℕ} [Fact p.Prime] {dK : ℕ} (ι : ℂ ≃+* ℂ_[p])

theorem padic_norm_twelve_eq_one_of_five_le (hp : p = 3) {r : ℤ} (hr : r = 1 ∨ r = 2) : ‖(r : ℂ_[p])‖ = 1 := by
  apply normZ_one
  rw [hp]
  rcases hr with rfl | rfl <;> norm_num

theorem pick3 (hp : p = 3) {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) :
    ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ ‖x - (r : ℂ_[p])‖ = 1 := by
  have le1 : ∀ k : ℤ, ‖x - (k : ℂ_[p])‖ ≤ 1 := fun k => norm_sub_le_one hx (normZ_le k)
  by_cases h1 : ‖x - ((1 : ℤ) : ℂ_[p])‖ < 1
  · refine ⟨2, Or.inr rfl, le_antisymm (le1 2) (not_lt.1 fun h2 => ?_)⟩
    have h3 := IsUltrametricDist.norm_add_le_max (x - ((1 : ℤ) : ℂ_[p])) (-(x - ((2 : ℤ) : ℂ_[p])))
    have e : x - ((1 : ℤ) : ℂ_[p]) + -(x - ((2 : ℤ) : ℂ_[p])) = ((1 : ℤ) : ℂ_[p]) := by
      push_cast
      ring
    rw [e, padic_norm_twelve_eq_one_of_five_le hp (Or.inl rfl), norm_neg] at h3
    exact absurd h3 (not_le.2 (max_lt h1 h2))
  · exact ⟨1, Or.inl rfl, le_antisymm (le1 1) (not_lt.1 h1)⟩

theorem em_fst (a : ℤ × ℤ) : (em dK ι a).1 = (a.1 : ℂ_[p]) + (a.2 : ℂ_[p]) * ι (omegaK dK) := by
  show ι _ = _
  simp [map_add, map_mul, map_intCast]

theorem em_snd (a : ℤ × ℤ) :
    (em dK ι a).2 = (a.1 : ℂ_[p]) + (a.2 : ℂ_[p]) * (1 - ι (omegaK dK)) := by
  show ι _ = _
  simp [map_add, map_mul, map_intCast, map_sub, map_one]

theorem cand3 (hw : ‖ι (omegaK dK)‖ < 1 ∨ ‖ι (omegaK dK) - 1‖ < 1) (r s : ℤ) (hr : r = 1 ∨ r = 2)
    (hs : s = 1 ∨ s = 2) :
    ∃ a : ℤ × ℤ, ‖(em dK ι a).1 - (r : ℂ_[p])‖ < 1 ∧ ‖(em dK ι a).2 - (s : ℂ_[p])‖ < 1 := by
  have diag : ∀ k : ℤ, ‖(em dK ι (k, 0)).1 - (k : ℂ_[p])‖ < 1 ∧
      ‖(em dK ι (k, 0)).2 - (k : ℂ_[p])‖ < 1 := by
    intro k
    rw [em_fst, em_snd]
    simp
  have hwn : (‖ι (omegaK dK)‖ < 1 → ‖-ι (omegaK dK)‖ < 1) ∧
      (‖ι (omegaK dK) - 1‖ < 1 → ‖-(ι (omegaK dK) - 1)‖ < 1) :=
    ⟨fun h => by rwa [norm_neg], fun h => by rwa [norm_neg]⟩
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨_, diag 1⟩
  · rcases hw with hw | hw
    · refine ⟨(1, 1), ?_, ?_⟩
      · rw [em_fst]; convert hw using 2; push_cast; try ring
      · rw [em_snd]; convert hwn.1 hw using 2; push_cast; try ring
    · refine ⟨(2, -1), ?_, ?_⟩
      · rw [em_fst]; convert hwn.2 hw using 2; push_cast; try ring
      · rw [em_snd]; convert hw using 2; push_cast; try ring
  · rcases hw with hw | hw
    · refine ⟨(2, -1), ?_, ?_⟩
      · rw [em_fst]; convert hwn.1 hw using 2; push_cast; try ring
      · rw [em_snd]; convert hw using 2; push_cast; try ring
    · refine ⟨(1, 1), ?_, ?_⟩
      · rw [em_fst]; convert hw using 2; push_cast; try ring
      · rw [em_snd]; convert hwn.2 hw using 2; push_cast; try ring
  · exact ⟨_, diag 2⟩

theorem two_units3 (hmod : dK % 4 = 3) (hp : p = 3)
    (hw : ‖ι (omegaK dK)‖ < 1 ∨ ‖ι (omegaK dK) - 1‖ < 1) (α : OO ι hmod) :
    ∃ u v : (OO ι hmod)ˣ, α = u + v := by
  obtain ⟨ha, hb⟩ := norm_le ι hmod α.2
  obtain ⟨r, hr, har⟩ := pick3 hp ha
  obtain ⟨s, hs, hbs⟩ := pick3 hp hb
  obtain ⟨n, h1, h2⟩ := cand3 ι hw r s hr hs
  have hc1 : ‖(em dK ι n).1‖ = 1 := norm_one_of_close h1 (padic_norm_twelve_eq_one_of_five_le hp hr)
  have hc2 : ‖(em dK ι n).2‖ = 1 := norm_one_of_close h2 (padic_norm_twelve_eq_one_of_five_le hp hs)
  have hd1 : ‖α.1.1 - (em dK ι n).1‖ = 1 := by
    refine norm_one_of_close (b := α.1.1 - (r : ℂ_[p])) ?_ har
    rw [show α.1.1 - (em dK ι n).1 - (α.1.1 - (r : ℂ_[p])) = -((em dK ι n).1 - (r : ℂ_[p])) by ring,
      norm_neg]
    exact h1
  have hd2 : ‖α.1.2 - (em dK ι n).2‖ = 1 := by
    refine norm_one_of_close (b := α.1.2 - (s : ℂ_[p])) ?_ hbs
    rw [show α.1.2 - (em dK ι n).2 - (α.1.2 - (s : ℂ_[p])) = -((em dK ι n).2 - (s : ℂ_[p])) by ring,
      norm_neg]
    exact h2
  set c : OO ι hmod := ⟨em dK ι n, em_mem ι hmod n⟩
  have hu : IsUnit c := isUnit_of_norm ι hmod c hc1 hc2
  have hv : IsUnit (α - c) := isUnit_of_norm ι hmod (α - c) hd1 hd2
  refine ⟨hv.unit, hu.unit, ?_⟩
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  ring

theorem three_split (hpd : ¬ (3 : ℤ) ∣ (dK : ℤ)) (hmod : dK % 4 = 3) {m n : ℤ}
    (hN : (3 : ℤ) ∣ normInt dK m n) (hmn : ¬ ((3 : ℤ) ∣ m ∧ (3 : ℤ) ∣ n)) :
    (3 : ℤ) ∣ ((dK : ℤ) + 1) / 4 := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hdiv : ((dK : ℤ) + 1) / 4 = k := by omega
  have hd : (dK : ℤ) = 4 * k - 1 := by omega
  unfold normInt at hN
  rw [hdiv] at hN ⊢
  rw [hd] at hpd
  have e : ∀ x : ℤ, (3 : ℤ) ∣ x ↔ ((x : ZMod 3) = 0) := fun x => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  rw [e] at hN hpd ⊢
  rw [e, e] at hmn
  push_cast at hN hpd hmn
  have key : ∀ a b c : ZMod 3, a ^ 2 + a * b + b ^ 2 * c = 0 → ¬ (4 * c - 1 = 0) →
      ¬ (a = 0 ∧ b = 0) → c = 0 := by decide
  exact key _ _ _ hN hpd hmn

end Three

theorem calcGen {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {dK : ℕ} (L : PeriodPair) (hmod : dK % 4 = 3)
    (hcm : HasCMBy dK L) (hp2 : p ≠ 2) (hW : IntCurve (curveL p L ι))
    (htwo : ∀ α : OO ι hmod, ∃ u v : (OO ι hmod)ˣ, α = u + v) (a b : ℂ_[p]) (hab : (a, b) ∈ OO ι hmod) :
    EndInt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) a ∧
    PhNormAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι))
      (Formalism.L2.Th1.Top.phC p L ι) a b := by
  have h2 : ‖(2 : ℂ_[p])‖ = 1 := Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_two p hp2
  have hM : Formalism.L2.Th1.A.IntModel (curveL p L ι) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  let _ : StarRing (OO ι hmod) := starOO ι hmod
  have key := (Formalism.L2.Th1.C.curveEndoUnitBall ℂ_[p] h2 _ hM (ι (Formalism.L2.Th1.F.s2 L)) (OO ι hmod)
    (tau ι hmod)
    (continuous_fst.comp continuous_subtype_val)
    (Continuous.subtype_mk (continuous_swap.comp continuous_subtype_val) _)
    (fun z hz => selfadj ι hmod hp2 z.2 (congrArg Subtype.val hz))
    (isUnit_of_norm ι hmod 2 h2 h2)
    htwo
    (Dn ι hmod) (dense ι hmod)
    (by
      intro α hα
      obtain ⟨⟨m, n⟩, hN, hα⟩ := hα
      obtain ⟨S, neg, xP, yP, g1, g2, g3, g4, g5⟩ :=
        Formalism.L2.Th1.Top.CMDatum_proof dK L hmod hcm p ι hW m n hN
      have t1 : tau ι hmod α = ι ((m : ℂ) + (n : ℂ) * omegaK dK) := congrArg Prod.fst hα
      have t2 : tau ι hmod (star α) = ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) :=
        congrArg Prod.snd hα
      refine ⟨S, inferInstance, neg, xP, yP, ?_, g2, g3, ?_, ?_, ?_, ?_⟩
      · rw [t1]
        exact g1
      · rw [t1, t2]
        exact g4
      · rw [t1]
        exact Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_eq_one_of_quad (em_sum ι (m, n)) (em_prod ι hmod (m, n))
          (normZ_one hN)
      · rw [hb2]
        simp
      · rw [t1, t2]
        exact g5)).1
  have h := key ⟨(a, b), hab⟩
  exact ⟨h.1, h.2.1⟩

theorem split_w {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {dK : ℕ} (hmod : dK % 4 = 3) (hp : p = 3)
    (hpd : ¬ p ∣ dK) {m n : ℤ} (hN : (p : ℤ) ∣ normInt dK m n)
    (hα1 : ‖ι ((m : ℂ) + (n : ℂ) * omegaK dK)‖ = 1) :
    ‖ι (omegaK dK)‖ < 1 ∨ ‖ι (omegaK dK) - 1‖ < 1 := by
  have h3 : ‖((3 : ℤ) : ℂ_[p])‖ < 1 := normZ_lt.2 (by rw [hp]; norm_num)
  have hmn : ¬ ((3 : ℤ) ∣ m ∧ (3 : ℤ) ∣ n) := by
    rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    have e : ι (((3 * a : ℤ) : ℂ) + ((3 * b : ℤ) : ℂ) * omegaK dK) =
        ((3 : ℤ) : ℂ_[p]) * (em dK ι (a, b)).1 := by
      rw [em_fst]
      simp only [map_add, map_mul, map_intCast]
      push_cast
      ring
    rw [e, norm_mul] at hα1
    have hle := (em_norm_le ι hmod (a, b)).1
    have : ‖((3 : ℤ) : ℂ_[p])‖ * ‖(em dK ι (a, b)).1‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hle) h3
    linarith
  have hpd' : ¬ (3 : ℤ) ∣ (dK : ℤ) := by
    intro h
    apply hpd
    rw [hp]
    exact_mod_cast h
  have hN' : (3 : ℤ) ∣ normInt dK m n := by
    rw [hp] at hN
    exact_mod_cast hN
  have hc := three_split hpd' hmod hN' hmn
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hdiv : ((dK : ℤ) + 1) / 4 = k := by omega
  rw [hdiv] at hc
  have hkC : (1 + (dK : ℂ)) / 4 = (k : ℂ) := by
    have : ((dK : ℤ) : ℂ) + 1 = 4 * (k : ℂ) := by exact_mod_cast hk
    push_cast at this
    linear_combination this / 4
  have hprod : ι (omegaK dK) * (ι (omegaK dK) - 1) = -((k : ℤ) : ℂ_[p]) := by
    rw [show ι (omegaK dK) * (ι (omegaK dK) - 1) = ι (omegaK dK * (omegaK dK - 1)) by
      rw [map_mul, map_sub, map_one]]
    rw [show omegaK dK * (omegaK dK - 1) = -((k : ℤ) : ℂ) by
      linear_combination Formalism.L2.Th1.D.CurveNormEndomorphisms.omega_sq dK - hkC]
    rw [map_neg, map_intCast]
  have hn : ‖ι (omegaK dK) * (ι (omegaK dK) - 1)‖ < 1 := by
    rw [hprod, norm_neg]
    exact normZ_lt.2 (by rw [hp]; exact_mod_cast hc)
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  rw [norm_mul] at hn
  nlinarith [hcon.1, hcon.2]

theorem main_case {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {dK : ℕ} (L : PeriodPair) (hmod : dK % 4 = 3)
    (hcm : HasCMBy dK L) (hW : IntCurve (curveL p L ι)) (m n : ℤ)
    (hα1 : ‖ι ((m : ℂ) + (n : ℂ) * omegaK dK)‖ = 1)
    (hEI : EndInt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι))
        (ι ((m : ℂ) + (n : ℂ) * omegaK dK)) ∧
      PhNormAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι))
        (Formalism.L2.Th1.Top.phC p L ι) (ι ((m : ℂ) + (n : ℂ) * omegaK dK))
        (ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))))
    (t : ℂ) (hαt : ((m : ℂ) + (n : ℂ) * omegaK dK) * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    ‖px (curveL p L ι) (ptOf p L ι t)‖ ≤ 1 ∧ ‖py (curveL p L ι) (ptOf p L ι t)‖ ≤ 1 := by
  have hα0p : ι ((m : ℂ) + (n : ℂ) * omegaK dK) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα1
    exact zero_ne_one hα1
  have hα0 : (m : ℂ) + (n : ℂ) * omegaK dK ≠ 0 := by
    intro h
    rw [h, map_zero] at hα0p
    exact hα0p rfl
  have hmn : (m, n) ≠ (0, 0) := by
    intro h
    rw [Prod.mk.injEq] at h
    apply hα0
    rw [h.1, h.2]
    simp
  have hd : 0 < dK := by omega
  obtain ⟨S, hS, hcard, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm m n hmn hd
  obtain ⟨hst, -⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hcm m n
  have hprod : ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (S.card : ℂ) + 1 := by
    rw [Formalism.L2.Th1.D.CurveNormEndomorphisms.mul_bar]
    have := congrArg (fun x : ℝ => (x : ℂ)) hcard
    push_cast at this
    rw [this]
  have hcardS : ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (Fintype.card S : ℂ) + 1 := by
    rw [Fintype.card_coe]
    exact hprod
  obtain ⟨neg, -, hE⟩ := Formalism.L2.Th1.F.endoZInstance L _ S hα0 hst hS
  have hE0 : IsEndoZ (Formalism.L2.Th1.F.pSeries L) neg (fun P : S => L.weierstrassP (P : ℂ) + 0)
      (fun P : S => Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))
      ((m : ℂ) + (n : ℂ) * omegaK dK) := by
    simpa using hE
  have hs2C := (Formalism.L2.Th1.C.isogenyIffBar ℂ (Formalism.L2.Th1.F.pSeries L) (Formalism.L2.Th1.F.s2 L) S neg
    (fun P : S => L.weierstrassP (P : ℂ)) 0 _ _ _ hα0 hcardS hE0).1 (by simpa using hIso)
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  have hΔ : (curveL p L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hEp := Formalism.L2.Th1.D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
  rw [← Formalism.L2.Th1.E.wpBridge p L ι] at hEp
  have hEp' : IsEndoZ (wpReg (curveL p L ι)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ)) + (curveL p L ι).b₂ / 12)
      (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
      (ι ((m : ℂ) + (n : ℂ) * omegaK dK)) := by
    rw [hb2]
    simpa using hEp
  have hNp : ι ((m : ℂ) + (n : ℂ) * omegaK dK) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (Fintype.card S : ℂ_[p]) + 1 := by
    rw [← map_mul, hcardS]
    simp
  have hs2p : ι ((m : ℂ) + (n : ℂ) * omegaK dK) *
      (ι ((m : ℂ) + (n : ℂ) * omegaK dK) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))) *
      ι (Formalism.L2.Th1.F.s2 L) = ∑ P : S, (ι (L.weierstrassP (P : ℂ)) + (curveL p L ι).b₂ / 12) := by
    rw [hb2]
    have := congrArg ι hs2C
    simpa [map_mul, map_sub, map_sum] using this
  have hIsoP := (Formalism.L2.Th1.C.isogenyIffBar ℂ_[p] (wpReg (curveL p L ι)) (ι (Formalism.L2.Th1.F.s2 L)) S neg
    (fun P : S => ι (L.weierstrassP (P : ℂ))) ((curveL p L ι).b₂ / 12) _ _ _ hα0p hNp hEp').2 hs2p
  obtain ⟨hLP, hXW, hA, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (unitBall ℂ_[p]) (curveL p L ι)
    (Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.coeffIn hW)
  have hPh := (Formalism.L2.Th1.C.phOIsPh ℂ_[p] (wpReg (curveL p L ι)) (logSer (curveL p L ι))
    (ι (Formalism.L2.Th1.F.s2 L)) hLP.1 hLP.2.1).2
  have hU := Formalism.L2.Th1.C.isogenyU ℂ_[p] (wpReg (curveL p L ι)) (ι (Formalism.L2.Th1.F.s2 L))
    (logSer (curveL p L ι)) (expSer (curveL p L ι)) _ (xS (curveL p L ι)) ((curveL p L ι).b₂ / 12) S
    (fun P : S => ι (L.weierstrassP (P : ℂ))) _ hLP hPh hXW hIsoP
  have hali : (ι ((m : ℂ) + (n : ℂ) * omegaK dK))⁻¹ ∈ unitBall ℂ_[p] :=
    Formalism.L2.Th1.C.inv_mem_unitBall hα1
  have hPi := prod_int (unitBall ℂ_[p]) (mulBy (logSer (curveL p L ι)) (expSer (curveL p L ι))
      (ι ((m : ℂ) + (n : ℂ) * omegaK dK))) (Formalism.L2.Th1.Top.phC p L ι) (xS (curveL p L ι))
    (fun P : S => ι (L.weierstrassP (P : ℂ))) _ ((Fintype.card S : ℂ_[p]) + 1) hα0p hali
    (Formalism.L2.Th1.C.Pts.constantCoeff_mulBy hLP _) hEI.1 hPh.1 (by rw [← hNp]; exact hEI.2) hU
  have hxP := gauss_roots (xS (curveL p L ι)) hA.1 (fun n => hA.2 n)
    (fun P : S => ι (L.weierstrassP (P : ℂ))) (fun n => hPi n)
  obtain ⟨P, hP, htP⟩ := hS.2.2 t hαt ht
  have hwp : L.weierstrassP t = L.weierstrassP P := by
    have e : t = P + ((⟨t - P, htP⟩ : L.lattice) : ℂ) := by simp
    rw [e, L.weierstrassP_add_coe]
  have hx : ‖ι (L.weierstrassP t)‖ ≤ 1 := by
    rw [hwp]
    exact hxP ⟨P, hP⟩
  rw [Formalism.L2.Th1.E.ScaledModelNorms.px_ptOf p L ι hΔ t ht, Formalism.L2.Th1.E.ScaledModelNorms.py_ptOf p L ι hΔ t ht]
  refine ⟨hx, ?_⟩
  have heq := (Formalism.L2.Th1.E.ScaledModelNorms.nonsing p L ι hΔ t ht).1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  have h1 : (curveL p L ι).a₁ = 0 := rfl
  have h2 : (curveL p L ι).a₂ = 0 := rfl
  have h3 : (curveL p L ι).a₃ = 0 := rfl
  rw [h1, h2, h3] at heq
  have hy2 : (ι (L.derivWeierstrassP t) / 2) ^ 2 = ι (L.weierstrassP t) ^ 3 +
      (curveL p L ι).a₄ * ι (L.weierstrassP t) + (curveL p L ι).a₆ := by
    linear_combination heq
  have hn : ‖(ι (L.derivWeierstrassP t) / 2) ^ 2‖ ≤ 1 := by
    rw [hy2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) hW.2.2.2.2.1)
    · rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    · rw [norm_mul]
      exact mul_le_one₀ hW.2.2.2.1 (norm_nonneg _) hx
  rw [norm_pow] at hn
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hn

end UnitKernelIntegral

open UnitKernelIntegral Formalism.L2.Th1.Top.CalcPAux in
open Formalism.L2.Th1.CM (omegaK) in
open Formalism.L2.Th1.D (normInt) in

theorem unit_kernel_integral_coords : UnitKerInt := by
  intro dK L _hsq hmod hcm p _ ι hp2 hpd hW α t hαQ hα1 hαt ht
  obtain ⟨m, n, rfl⟩ := hαQ
  by_cases hN : (p : ℤ) ∣ normInt dK m n
  swap
  · exact Formalism.L2.Th1.E.kernelPtInt dK L hmod hcm p ι hW m n t hαt hN ht
  have hmem : (ι ((m : ℂ) + (n : ℂ) * omegaK dK), ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))) ∈ OO ι hmod :=
    em_mem ι hmod (m, n)
  have htwo : ∀ β : OO ι hmod, ∃ u v : (OO ι hmod)ˣ, β = u + v := by
    by_cases h5 : 5 ≤ p
    · exact two_units ι hmod h5
    · have hpr : p.Prime := Fact.out
      have hp3 : p = 3 := by
        have h2 := hpr.two_le
        rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with h | h | h
        · exact absurd h hp2
        · exact h
        · exfalso
          rw [h] at hpr
          norm_num at hpr
      exact two_units3 ι hmod hp3 (split_w ι hmod hp3 hpd hN hα1)
  exact main_case ι L hmod hcm hW m n hα1 (calcGen ι L hmod hcm hp2 hW htwo _ _ hmem) t hαt ht

end Formalism.L2.AlgTh
