import Formalism.LocalToGlobal.AlgebraicTheory.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSys
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussOrthOf

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

namespace TorsionPointJets

open PowerSeries
open Formalism.L2.Th1.G (JetsIn)
open Formalism.L2.Th1.C (IsLogPair IsOneUnit IntPS jet)

section Field

variable {K : Type} [Field K]

theorem mfact_single (n : ℕ) : Formalism.DworkPowerSeriesWeights.mfact (Finsupp.single () n) = n.factorial := by
  unfold Formalism.DworkPowerSeriesWeights.mfact
  exact Finsupp.prod_single_index (by simp)

theorem jets_in_iff_factorial_coeff (R : Subring K) (f : PowerSeries K) :
    JetsIn R (f : MvPowerSeries Unit K) ↔
      ∀ n : ℕ, ((n.factorial : ℕ) : K) * coeff n f ∈ R := by
  unfold JetsIn
  constructor
  · intro h n
    have h1 := h (Finsupp.single () n)
    rw [mfact_single] at h1
    exact h1
  · intro h κ
    obtain ⟨n, rfl⟩ : ∃ n, κ = Finsupp.single () n := ⟨κ (), Finsupp.ext fun u => by cases u; simp⟩
    rw [mfact_single]
    exact h n

theorem jet_derivative (f : PowerSeries K) (n : ℕ) :
    ((n.factorial : ℕ) : K) * coeff n (derivative K f) =
      (((n + 1).factorial : ℕ) : K) * coeff (n + 1) f := by
  rw [coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

theorem jetsIn_derivative {R : Subring K} {f : PowerSeries K}
    (hf : JetsIn R (f : MvPowerSeries Unit K)) :
    JetsIn R ((derivative K f : PowerSeries K) : MvPowerSeries Unit K) := by
  rw [jets_in_iff_factorial_coeff] at hf ⊢
  intro n
  rw [jet_derivative]
  exact hf (n + 1)

theorem subst_one' {e : PowerSeries K} (hs : HasSubst e) : subst e (1 : PowerSeries K) = 1 := by
  rw [← coe_substAlgHom hs, map_one]

theorem subst_neg' {e : PowerSeries K} (hs : HasSubst e) (f : PowerSeries K) :
    subst e (-f) = -subst e f := by
  rw [← coe_substAlgHom hs, map_neg]

theorem subst_e_l {l e : PowerSeries K} (h : IsLogPair l e) (F : PowerSeries K) :
    subst e (subst l F) = F := by
  obtain ⟨hl0, -, he0, -, hel⟩ := h
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hl0)
    (HasSubst.of_constantCoeff_zero' he0), hel]
  exact X_subst F

private theorem derivative_subst_eq_subst_Dinv {l e : PowerSeries K} (h : IsLogPair l e) (g : PowerSeries K) :
    derivative K (subst e g) = subst e (Formalism.L2.Th1.C.Dinv l g) := by
  obtain ⟨-, hl1, he0, -, hel⟩ := h
  have hse : HasSubst e := HasSubst.of_constantCoeff_zero' he0
  have hc : constantCoeff (derivative K l) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp [hl1]
  have h1 : subst e (derivative K l) * derivative K e = 1 := by
    rw [← derivative_subst hse, hel, derivative_X]
  have h2 : subst e ((derivative K l)⁻¹) * subst e (derivative K l) = 1 := by
    rw [← coe_substAlgHom hse, ← map_mul, PowerSeries.inv_mul_cancel _ hc, map_one]
  have h3 : derivative K e = subst e ((derivative K l)⁻¹) := by
    calc derivative K e
        = (subst e ((derivative K l)⁻¹) * subst e (derivative K l)) * derivative K e := by
          rw [h2, one_mul]
      _ = subst e ((derivative K l)⁻¹) * (subst e (derivative K l) * derivative K e) := by ring
      _ = subst e ((derivative K l)⁻¹) := by rw [h1, mul_one]
  rw [derivative_subst hse, h3]
  unfold Formalism.L2.Th1.C.Dinv
  rw [← coe_substAlgHom hse, map_mul]
  ring

private theorem iterate_derivative_subst_eq_subst_iterate {l e : PowerSeries K} (h : IsLogPair l e) (n : ℕ) (g : PowerSeries K) :
    (derivative K)^[n] (subst e g) = subst e ((Formalism.L2.Th1.C.Dinv l)^[n] g) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_subst_eq_subst_Dinv h, ih]

private theorem factorial_mul_coeff_eq_constantCoeff_iterate (n : ℕ) (g : PowerSeries K) :
    ((n.factorial : ℕ) : K) * coeff n g = constantCoeff ((derivative K)^[n] g) := by
  induction n generalizing g with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n ih => rw [Function.iterate_succ_apply, ← ih, jet_derivative]

private theorem factorial_mul_coeff_subst_eq_jet {l e : PowerSeries K} (h : IsLogPair l e) (g : PowerSeries K) (n : ℕ) :
    ((n.factorial : ℕ) : K) * coeff n (subst e g) = jet l g n := by
  have he0 : constantCoeff e = 0 := h.2.2.1
  rw [factorial_mul_coeff_eq_constantCoeff_iterate, iterate_derivative_subst_eq_subst_iterate h, Formalism.L2.Th1.A.ZSer.cc_subst he0]
  rfl

theorem jetsIn_subst_int {R : Subring K} {l e V : PowerSeries K} (h : IsLogPair l e)
    (hu : IsOneUnit R (derivative K l)) (hV : IntPS R V) :
    JetsIn R ((subst e V : PowerSeries K) : MvPowerSeries Unit K) := by
  rw [jets_in_iff_factorial_coeff]
  intro n
  rw [factorial_mul_coeff_subst_eq_jet h]
  exact Formalism.L2.Th1.G.intDJets K R l V hu hV n

theorem jetsIn_subst_ph {R : Subring K} {l e ph : PowerSeries K} (h : IsLogPair l e)
    (h0 : constantCoeff ph = 0) (hj : ∀ i, 1 ≤ i → jet l ph i ∈ R) :
    JetsIn R ((subst e ph : PowerSeries K) : MvPowerSeries Unit K) := by
  rw [jets_in_iff_factorial_coeff]
  intro n
  rw [factorial_mul_coeff_subst_eq_jet h]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show constantCoeff ph ∈ R
    rw [h0]
    exact R.zero_mem
  · exact hj n hn

variable [CharZero K]

theorem jetsIn_subst_fExp {R : Subring K} {l e ph : PowerSeries K} (h : IsLogPair l e)
    (h0 : constantCoeff ph = 0) (hj : JetsIn R ((subst e ph : PowerSeries K) : MvPowerSeries Unit K)) :
    JetsIn R ((subst e (Formalism.L2.Th1.B.fExp ph) : PowerSeries K) : MvPowerSeries Unit K) := by
  have he0 : constantCoeff e = 0 := h.2.2.1
  have hse : HasSubst e := HasSubst.of_constantCoeff_zero' he0
  have hph : HasSubst ph := HasSubst.of_constantCoeff_zero' h0
  have key : subst e (Formalism.L2.Th1.B.fExp ph) =
      Formalism.L2.Th1.C.mvExp (subst e ph : MvPowerSeries Unit K) := by
    unfold Formalism.L2.Th1.B.fExp Formalism.L2.Th1.C.mvExp
    rw [subst_comp_subst_apply hph hse]
  have hcc : MvPowerSeries.constantCoeff (subst e ph : MvPowerSeries Unit K) = 0 := by
    have := Formalism.L2.Th1.A.ZSer.cc_subst (g := ph) he0
    rw [h0] at this
    exact this
  rw [key]
  exact Formalism.L2.Th1.G.jetsExp K R Unit _ hcc hj

end Field

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem mem_ball (x : K) : x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem norm_jets {f : PowerSeries K} (hf : JetsIn (Formalism.G.unitBall K) (f : MvPowerSeries Unit K)) (n : ℕ) :
    ‖((n.factorial : ℕ) : K) * coeff n f‖ ≤ 1 := by
  exact (jets_in_iff_factorial_coeff _ f).mp hf n

theorem core_zero {l e ph Fz G : PowerSeries K} (h : IsLogPair l e)
    (hu : IsOneUnit (Formalism.G.unitBall K) (derivative K l)) (h0 : constantCoeff ph = 0)
    (hj : ∀ i, 1 ≤ i → jet l ph i ∈ Formalism.G.unitBall K)
    (hG : G = Formalism.L2.Th1.B.fExp ph * subst l Fz) (ε : K) (hε : ‖ε‖ ≤ 1) (hGe : G = C ε * X) :
    ∀ n, ‖((n.factorial : ℕ) : K) * coeff n Fz‖ ≤ 1 := by
  have he0 : constantCoeff e = 0 := h.2.2.1
  have hse : HasSubst e := HasSubst.of_constantCoeff_zero' he0
  have JR := Formalism.L2.Th1.G.jetsRing K (Formalism.G.unitBall K) Unit
  have hEL := Formalism.L2.Th1.B.expLogRules K Unit

  have hexp0 : Formalism.L2.Th1.B.fExp (0 : PowerSeries K) = 1 := by
    rw [← Formalism.L2.Th1.B.Add1.fLog_one Formalism.L2.Th1.B.expLogRules]
    exact (hEL.2.2 1 (by simp)).2
  have hinv : Formalism.L2.Th1.B.fExp ph * Formalism.L2.Th1.B.fExp (-ph) = 1 := by
    rw [← hEL.1 ph (-ph) h0 (by rw [map_neg, neg_eq_zero]; exact h0), add_neg_cancel]
    exact hexp0
  have h1 : subst l Fz = G * Formalism.L2.Th1.B.fExp (-ph) := by
    rw [hG, mul_comm (Formalism.L2.Th1.B.fExp ph), mul_assoc, hinv, mul_one]
  have h2 : Fz = subst e (C ε * X) * subst e (Formalism.L2.Th1.B.fExp (-ph)) := by
    rw [← subst_e_l h Fz, h1, hGe, ← coe_substAlgHom hse, map_mul]

  have hV : IntPS (Formalism.G.unitBall K) (C ε * X) := by
    intro n
    rw [coeff_C_mul, coeff_X]
    split_ifs
    · rw [mul_one, mem_ball]; exact hε
    · rw [mul_zero]; exact (Formalism.G.unitBall K).zero_mem
  have hA := jetsIn_subst_int h hu hV
  have hj' : JetsIn (Formalism.G.unitBall K) ((subst e (-ph) : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [subst_neg' hse]
    exact JR.2.2.2.1 _ (jetsIn_subst_ph h h0 hj)
  have hB := jetsIn_subst_fExp h (by simp [h0]) hj'
  have hFz : JetsIn (Formalism.G.unitBall K) (Fz : MvPowerSeries Unit K) := by
    rw [h2]
    exact JR.2.2.2.2 _ _ hA hB
  exact fun n => norm_jets hFz n

theorem core_pow (h2 : LogDerJets) (h3 : PowLogDer) {l e ph Fz G V : PowerSeries K} (h : IsLogPair l e)
    (hu : IsOneUnit (Formalism.G.unitBall K) (derivative K l)) (h0 : constantCoeff ph = 0)
    (hj : ∀ i, 1 ≤ i → jet l ph i ∈ Formalism.G.unitBall K)
    (hG : G = Formalism.L2.Th1.B.fExp ph * subst l Fz) (hF0 : ‖constantCoeff Fz‖ ≤ 1)
    (c : K) (hc : c ≠ 0) (M : ℕ) (hM : 0 < M) (hV0 : constantCoeff V = 1)
    (hVi : IntPS (Formalism.G.unitBall K) V) (hpow : G ^ M = C (c ^ M) * V) :
    ∀ n, ‖((n.factorial : ℕ) : K) * coeff n Fz‖ ≤ ‖(M : K)‖⁻¹ ^ n := by
  have hs : HasSubst e := Formalism.L2.Th1.C.JetSubstitutionLemmas.hs1 h.2.2.1
  have hMne : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hMpos : 0 < ‖(M : K)‖ := norm_pos_iff.2 hMne
  have hM1 : ‖(M : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K M
  have hρ : 1 ≤ ‖(M : K)‖⁻¹ := one_le_inv₀ hMpos |>.2 hM1
  have hVne : constantCoeff V ≠ 0 := by rw [hV0]; exact one_ne_zero
  have hVinv : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hVne
  have hWi : IntPS (Formalism.G.unitBall K) V⁻¹ := Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_of_mul_eq_one hVi hV0 hVinv
  set E : PowerSeries K := subst e (Formalism.L2.Th1.B.fExp ph) with hEdef
  set Ei : PowerSeries K := subst e (Formalism.L2.Th1.B.fExp (-ph)) with hEidef
  set Vz : PowerSeries K := subst e V with hVzdef
  set Wz : PowerSeries K := subst e V⁻¹ with hWzdef
  set Gz : PowerSeries K := subst e G with hGzdef
  have hGz : Gz = E * Fz := by
    rw [hGzdef, hG, subst_mul hs, subst_e_l h]
  have hpz : Gz ^ M = C (c ^ M) * Vz := by
    rw [hGzdef, ← subst_pow hs, hpow, subst_mul hs, subst_C]
    rfl
  have hPL := h3 K Gz Vz c M hM hc hpz
  have hEE : E * Ei = 1 := by
    rw [hEdef, hEidef, ← subst_mul hs, Formalism.L2.Th1.B.ParO.fExp_mul_neg h0, subst_one' hs]
  have hWW : Vz * Wz = 1 := by
    rw [hVzdef, hWzdef, ← subst_mul hs, hVinv, subst_one' hs]
  have hd : derivative K Gz = derivative K E * Fz + E * derivative K Fz := by
    rw [hGz, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [hd, hGz] at hPL
  have hMM : C (M : K) * C ((M : K)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hMne, map_one]
  set a : PowerSeries K := C ((M : K)⁻¹) * (derivative K Vz * Wz) - derivative K E * Ei with hadef
  have hFa : derivative K Fz = a * Fz := by
    rw [hadef]
    linear_combination (C ((M : K)⁻¹) * Ei * Wz) * hPL
      - (derivative K Fz + derivative K E * Ei * Fz) * hMM
      - (derivative K Fz + derivative K E * Ei * Fz) * (C (M : K) * C ((M : K)⁻¹)) * hWW
      + (C ((M : K)⁻¹) * derivative K Vz * Wz * Fz
          - derivative K Fz * (C (M : K) * C ((M : K)⁻¹)) * (Vz * Wz)) * hEE
  have h0' : constantCoeff (-ph) = 0 := by rw [map_neg, h0, neg_zero]
  have hJE : JetsIn (Formalism.G.unitBall K) (E : MvPowerSeries Unit K) :=
    jetsIn_subst_fExp h h0 (jetsIn_subst_ph h h0 hj)
  have hJEi : JetsIn (Formalism.G.unitBall K) (Ei : MvPowerSeries Unit K) := by
    refine jetsIn_subst_fExp h h0' ?_
    rw [subst_neg' hs]
    exact Formalism.L2.Th1.G.jetsIn_neg (jetsIn_subst_ph h h0 hj)
  have hJ1 : JetsIn (Formalism.G.unitBall K) ((derivative K Vz * Wz : PowerSeries K) : MvPowerSeries Unit K) :=
    Formalism.L2.Th1.G.jetsIn_mul (jetsIn_derivative (jetsIn_subst_int h hu hVi)) (jetsIn_subst_int h hu hWi)
  have hJ2 : JetsIn (Formalism.G.unitBall K) ((derivative K E * Ei : PowerSeries K) : MvPowerSeries Unit K) :=
    Formalism.L2.Th1.G.jetsIn_mul (jetsIn_derivative hJE) hJEi
  have ha : ∀ n : ℕ, ‖((n.factorial : ℕ) : K) * coeff n a‖ ≤ ‖(M : K)‖⁻¹ := by
    intro n
    have e1 : ((n.factorial : ℕ) : K) * coeff n a =
        (M : K)⁻¹ * (((n.factorial : ℕ) : K) * coeff n (derivative K Vz * Wz)) -
          ((n.factorial : ℕ) : K) * coeff n (derivative K E * Ei) := by
      rw [hadef, map_sub, coeff_C_mul]
      ring
    rw [e1, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_inv]
      calc ‖(M : K)‖⁻¹ * _ ≤ ‖(M : K)‖⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (norm_jets hJ1 n) (inv_nonneg.2 (norm_nonneg _))
        _ = ‖(M : K)‖⁻¹ := mul_one _
    · rw [norm_neg]
      exact (norm_jets hJ2 n).trans hρ
  exact h2 K Fz a ‖(M : K)‖⁻¹ hρ hFa hF0 ha

end Norm

end TorsionPointJets

open TorsionPointJets

theorem etJetsSigma_of (h1 : EtPower) (h2 : LogDerJets) (h3 : PowLogDer) : EtJetsSigma := by
  intro dK L hsq hmod hcm p _ ι hp2 hpd hW α t M hαq hα hαt hM hMt i
  obtain ⟨hlp, hu, -⟩ := Formalism.L2.Th1.Top.CAux.frame L ι hW
  have hph0 := Formalism.L2.Th1.E.AnaSys.cc_phL p L ι
  have hphC : Formalism.L2.Th1.Top.phC p L ι = Formalism.L2.Th1.E.phL p L ι := by
    unfold Formalism.L2.Th1.Top.phC Formalism.L2.Th1.E.phL
    rw [Formalism.L2.Th1.E.wpBridge p L ι]
  have hj : ∀ k, 1 ≤ k → Formalism.L2.Th1.C.jet (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.E.curveL p L ι))
      (Formalism.L2.Th1.E.phL p L ι) k ∈ Formalism.G.unitBall ℂ_[p] := by
    intro k hk
    rw [mem_ball, ← hphC]
    exact Formalism.L2.Th1.Top.jetsCM dK L hmod hcm p hp2 hpd ι hW k hk
  have hG : Formalism.L2.Th1.E.gT p L ι t = Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.E.phL p L ι) *
      PowerSeries.subst (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.E.curveL p L ι))
        (PowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L)))) := rfl
  have hjet : ∀ j : ℕ, ι (iteratedDeriv j (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L)) 0) =
      ((j.factorial : ℕ) : ℂ_[p]) * PowerSeries.coeff j (PowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L)))) := by
    intro j
    rw [PowerSeries.coeff_map, Formalism.L2.Th1.F.taylor0, PowerSeries.coeff_mk]
    simp only [RingEquiv.coe_toRingHom, map_div₀, map_natCast]
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j))]
  have hMpos : 0 < ‖(M : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hM.ne')
  have hM1 : ‖(M : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ M
  rw [hjet i]
  by_cases ht : t ∈ L.lattice
  · obtain ⟨ε, hε, hGe⟩ := Formalism.L2.Th1.E.AnaSys.gT_mem p L ι t ht
    have hb := core_zero hlp hu hph0 hj hG ε hε.le hGe i
    calc _ ≤ 1 * 1 := mul_le_mul hb (pow_le_one₀ (norm_nonneg _) hM1) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · obtain ⟨hc, V, ⟨hV0, hVi⟩, hpow⟩ := h1 dK L hsq hmod hcm p ι hp2 hpd hW α t M hαq hα hαt ht hM hMt
    have hc0 : ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hc
      exact zero_ne_one hc
    have hF0 : ‖PowerSeries.constantCoeff (PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))))‖ ≤ 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← one_mul (PowerSeries.coeff 0 _)]
      have e0 := hjet 0
      rw [Nat.factorial_zero, Nat.cast_one] at e0
      rw [← e0, iteratedDeriv_zero, hc]
    have hb := core_pow h2 h3 hlp hu hph0 hj hG hF0 _ hc0 M hM hV0 (fun n => (mem_ball _).2 (hVi n)) hpow i
    calc _ ≤ ‖(M : ℂ_[p])‖⁻¹ ^ i * ‖(M : ℂ_[p])‖ ^ i := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hMpos.ne', one_pow]

theorem etJetsTh0_of (h : EtJetsSigma) : EtJetsTh0 := by
  intro dK L hsq hmod hcm p _ ι hp2 hpd hW ω₀ hω hω2 α t M hαq hα hαt hM hMt i
  have h2n : ‖(2 : ℂ_[p])‖ = 1 := Formalism.L2.Th1.Top.CAux.norm_two hp2
  have hp2' : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 hd)
  have hMω : (M : ℂ) * ω₀ ∈ L.lattice := by
    have := L.lattice.nsmul_mem hω M
    rwa [nsmul_eq_mul] at this
  have hαω : α * ω₀ ∈ L.lattice := by
    obtain ⟨m, n, rfl⟩ := hαq
    have h1 := zsmul_mem hω m
    have h2 := zsmul_mem (hcm ω₀ hω) n
    have h3 := L.lattice.add_mem h1 h2
    simp only [zsmul_eq_mul] at h3
    convert h3 using 1
    ring
  have h2t : ((2 * M : ℕ) : ℂ) * t ∈ L.lattice := by
    have := L.lattice.add_mem hMt hMt
    convert this using 1
    push_cast
    ring
  have h2t0 : ((2 * M : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by
    convert hMω using 1
    push_cast
    ring
  obtain ⟨ζ, m, hm, hζ, hop⟩ := Formalism.L2.Th1.E.opUTh0Root L t (ω₀ / 2) (2 * M) (by omega) h2t h2t0 hω2
  have hc : ‖ι (Formalism.L2.Th1.F.opU L (ω₀ / 2) (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 := by
    refine (Formalism.L2.Th1.E.analyticTrans p L ι hW (ω₀ / 2) 2 two_pos hp2' ?_ hω2).1
    convert hω using 1
    push_cast
    ring
  have hζn : ‖ι ζ‖ = 1 := by
    have e : (ι ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have e2 : ‖ι ζ‖ ^ m = 1 := by rw [← norm_pow, e, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2
  have hq2 : IsQInt dK (2 * α) := by
    obtain ⟨m', n', rfl⟩ := hαq
    exact ⟨2 * m', 2 * n', by push_cast; ring⟩
  have hα2 : ‖ι (2 * α)‖ = 1 := by
    rw [map_mul, map_ofNat, norm_mul, h2n, hα, one_mul]
  have hαt2 : 2 * α * (t + ω₀ / 2) ∈ L.lattice := by
    have := L.lattice.add_mem (L.lattice.add_mem hαt hαt) hαω
    convert this using 1
    ring
  have hMt2 : ((2 * M : ℕ) : ℂ) * (t + ω₀ / 2) ∈ L.lattice := by
    have := L.lattice.add_mem (L.lattice.add_mem hMt hMt) hMω
    convert this using 1
    push_cast
    ring
  have hb := h dK L hsq hmod hcm p ι hp2 hpd hW (2 * α) (t + ω₀ / 2) (2 * M) hq2 hα2 hαt2 (by omega) hMt2 i
  have hnM : ‖((2 * M : ℕ) : ℂ_[p])‖ = ‖(M : ℂ_[p])‖ := by
    rw [Nat.cast_mul, Nat.cast_ofNat, norm_mul, h2n, one_mul]
  rw [hnM] at hb
  rw [hop, iteratedDeriv_const_mul_field, map_mul, norm_mul, map_mul, norm_mul, map_inv₀, norm_inv, hc, hζn,
    inv_one, one_mul, one_mul]
  exact hb

theorem etThetaZ_of (h : EtJetsTh0) (hp : ProdScaleJets) : EtThetaZ := by
  intro dK L hsq hmod hcm p _ ι hp2 hpd hW ω₀ hω hω2 κ n _ _ _ r s α M hαq hα hM hr hαs hMs
  unfold Formalism.L2.Th1.Top.thetaZ
  refine hp ℂ_[p] κ n (M : ℂ_[p]) r _ hr ?_
  intro k i j
  rw [PowerSeries.coeff_map, Formalism.L2.Th1.F.taylor0, PowerSeries.coeff_mk]
  simp only [RingEquiv.coe_toRingHom, map_div₀, map_natCast]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j))]
  exact h dK L hsq hmod hcm p ι hp2 hpd hW ω₀ hω hω2 α (s k i) M hαq hα (hαs k i) hM (hMs k i) j

end Formalism.L2.AlgTh
