import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalD

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg shortW)
open Formalism.L2.Th1.D (normInt)
open Formalism.G (unitBall)

namespace OrthogonalGaussModelNormLemmas

theorem norm_le_one_of_quad {K : Type} [NormedField K] [IsUltrametricDist K] {a b c : K} {t : ℤ}
    (hs : a + b = (t : K)) (hp : a * b = c) (hc : ‖c‖ ≤ 1) : ‖a‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have e : a ^ 2 = (t : K) * a - c := by
    rw [← hs, ← hp]
    ring
  have h1 : ‖a ^ 2‖ ≤ max ‖(t : K) * a‖ ‖c‖ := by
    rw [e, sub_eq_add_neg, ← norm_neg c]
    exact IsUltrametricDist.norm_add_le_max _ _
  have h2 : ‖(t : K) * a‖ ≤ ‖a‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K t)
  have h3 : ‖c‖ ≤ ‖a‖ := hc.trans h.le
  have h4 : ‖a‖ ^ 2 ≤ ‖a‖ := by
    rw [← norm_pow]
    exact h1.trans (max_le h2 h3)
  nlinarith

theorem norm_eq_one_of_quad {K : Type} [NormedField K] [IsUltrametricDist K] {a b c : K} {t : ℤ}
    (hs : a + b = (t : K)) (hp : a * b = c) (hc : ‖c‖ = 1) : ‖a‖ = 1 := by
  have ha := norm_le_one_of_quad hs hp hc.le
  have hb := norm_le_one_of_quad (a := b) (b := a) (by rw [add_comm]; exact hs)
    (by rw [mul_comm]; exact hp) hc.le
  have h : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hp, hc]
  refine le_antisymm ha ?_
  calc (1 : ℝ) = ‖a‖ * ‖b‖ := h.symm
    _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg a)
    _ = ‖a‖ := mul_one _

theorem norm_int (p : ℕ) [Fact p.Prime] {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : ‖(z : ℂ_[p])‖ = 1 := by
  have h1 : ¬ p ∣ z.natAbs := fun h2 => h (Int.natCast_dvd.2 h2)
  have h3 := Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h1
  rcases Int.natAbs_eq z with e | e
  · rw [e]
    simpa using h3
  · rw [e]
    simpa using h3

theorem norm_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ¬ p ∣ 2 := fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  simpa using Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h

theorem prod_bar {dK : ℕ} (hmod : dK % 4 = 3) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      ((normInt dK m n : ℤ) : ℂ) := by
  rw [Formalism.L2.Th1.D.CurveNormEndomorphisms.mul_bar]
  have := congrArg (fun x : ℝ => (x : ℂ)) (Formalism.L2.Th1.D.CurveNormEndomorphisms.normInt_cast hmod m n)
  push_cast at this
  rw [this]

theorem four_normInt {dK : ℕ} (hmod : dK % 4 = 3) (m : ℤ) :
    4 * normInt dK m 1 = (2 * m + 1) ^ 2 + (dK : ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hdiv : ((dK : ℤ) + 1) / 4 = k := by omega
  unfold normInt
  rw [hdiv]
  linear_combination -hk

variable {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])

theorem sum_bar (dK : ℕ) (m : ℤ) :
    ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) + ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK)) =
      ((2 * m + 1 : ℤ) : ℂ_[p]) := by
  rw [← map_add]
  have e : ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) + ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK)) =
      ((2 * m + 1 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [e, map_intCast]

theorem diff_sq (dK : ℕ) (m : ℤ) :
    (ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) - ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))) ^ 2 =
      -(dK : ℂ_[p]) := by
  rw [← map_sub, ← map_pow]
  have e : (((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) -
      ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))) ^ 2 = -(dK : ℂ) := by
    push_cast
    linear_combination 4 * Formalism.L2.Th1.D.CurveNormEndomorphisms.omega_sq dK
  rw [e, map_neg, map_natCast]

theorem norm_al {dK : ℕ} (hmod : dK % 4 = 3) (m : ℤ) (hN : ¬ (p : ℤ) ∣ normInt dK m 1) :
    ‖ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK)‖ = 1 := by
  refine norm_eq_one_of_quad (sum_bar ι dK m) (c := ((normInt dK m 1 : ℤ) : ℂ_[p])) ?_
    (norm_int p hN)
  rw [← map_mul, prod_bar hmod, map_intCast]

theorem coeffIn {W : WeierstrassCurve ℂ_[p]} (hW : IntCurve W) :
    Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[p]) W :=
  ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩

end OrthogonalGaussModelNormLemmas

theorem CMDatum_proof : CMDatum := by
  intro dK L hmod hCM p _ ι hW m n hN
  have hN0 : normInt dK m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩ :=
    Formalism.L2.Th1.D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  have hΔ : (curveL p L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  refine ⟨S, neg, fun P => ι (L.weierstrassP (P : ℂ)),
    fun P => ι (L.derivWeierstrassP (P : ℂ)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · apply Formalism.L2.Th1.D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) (curveL p L ι)
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (Formalism.L2.Th1.E.ScaledModelNorms.nonsing p L ι hΔ _ (hker P).2).1
    · intro P
      constructor
      · exact congrArg ι (hnegP P).1
      · simp only [WeierstrassCurve.Affine.negY, curveL, shortW]
        rw [(hnegP P).2, map_neg]
        ring
    · have h := Formalism.L2.Th1.D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, hb2, zero_div, add_zero]
      rw [Formalism.L2.Th1.E.wpBridge]
      exact h
  · intro P
    have h := (Formalism.L2.Th1.E.ptOfInt p L ι hW (P : ℂ) (S.card + 1) (Nat.succ_pos _) hpN
      (hker P).1 (hker P).2).1
    rwa [Formalism.L2.Th1.E.ScaledModelNorms.px_ptOf p L ι hΔ _ (hker P).2] at h
  · intro P
    have h := (Formalism.L2.Th1.E.ptOfInt p L ι hW (P : ℂ) (S.card + 1) (Nat.succ_pos _) hpN
      (hker P).1 (hker P).2).2
    rwa [Formalism.L2.Th1.E.ScaledModelNorms.py_ptOf p L ι hΔ _ (hker P).2] at h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp
  · rw [← map_sub, ← map_mul, ← map_mul, hs2C, map_sum, hb2]
    simp

theorem ShapeCM_of (hD : CMDatum) : ShapeCM := by
  intro dK L hmod hCM p _ hpd ι hW
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpd
    omega
  have hN : ¬ (p : ℤ) ∣ normInt dK 0 1 := by
    intro h
    have h4 := OrthogonalGaussModelNormLemmas.four_normInt hmod 0
    have h1 : (p : ℤ) ∣ (dK : ℤ) := by exact_mod_cast hpd
    have h2 : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = 4 * normInt dK 0 1 - dK := by linarith
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_left h 4) h1
    have h3 : p ∣ 1 := by exact_mod_cast h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ := hD dK L hmod hCM p ι hW 0 1 hN
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  exact Formalism.L2.Th1.G.curveRamified ℂ_[p] (curveL p L ι) (OrthogonalGaussModelNormLemmas.coeffIn hW)
    (OrthogonalGaussModelNormLemmas.norm_two p hp2) (ι (Formalism.L2.Th1.F.s2 L)) _ _ dK (2 * 0 + 1) S neg xP yP hE hx hy hprod
    (OrthogonalGaussModelNormLemmas.norm_al ι hmod 0 hN) (OrthogonalGaussModelNormLemmas.sum_bar ι dK 0) (OrthogonalGaussModelNormLemmas.diff_sq ι dK 0)
    (by omega) (by rw [hb2]; simp) hs

theorem JetsCM_of (hD : CMDatum) : JetsCM := by
  intro dK L hmod hCM p _ hp2 hpd ι hW
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (p : ℤ) = 2 * m + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact ⟨(p : ℤ) / 2, by omega⟩
  have hN : ¬ (p : ℤ) ∣ normInt dK m 1 := by
    intro h
    have h4 := OrthogonalGaussModelNormLemmas.four_normInt hmod m
    apply hpd
    have h2 : (p : ℤ) ∣ (dK : ℤ) := by
      have e : (dK : ℤ) = 4 * normInt dK m 1 - (p : ℤ) * (p : ℤ) := by
        rw [h4, hm]
        ring
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_left h 4) (Dvd.intro _ rfl)
    exact_mod_cast h2
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ := hD dK L hmod hCM p ι hW m 1 hN
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  have hdiff : ‖ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) -
      ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))‖ = 1 := by
    have h1 := congrArg norm (OrthogonalGaussModelNormLemmas.diff_sq ι dK m)
    rw [norm_pow, norm_neg, Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p hpd] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  exact Formalism.L2.Th1.G.curveJetsUnramThm ℂ_[p] (curveL p L ι) (OrthogonalGaussModelNormLemmas.coeffIn hW)
    (OrthogonalGaussModelNormLemmas.norm_two p hp2) (ι (Formalism.L2.Th1.F.s2 L)) _ _ (2 * m + 1) S neg xP yP hE hx hy hprod
    (OrthogonalGaussModelNormLemmas.norm_al ι hmod m hN) (OrthogonalGaussModelNormLemmas.sum_bar ι dK m) hdiff (by rw [hb2]; simp) hs

end Formalism.L2.Th1.Top
