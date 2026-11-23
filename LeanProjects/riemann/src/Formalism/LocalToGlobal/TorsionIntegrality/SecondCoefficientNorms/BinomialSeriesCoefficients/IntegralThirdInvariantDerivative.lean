import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.ThirdJetIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.SigmaConstantAgrees

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

namespace FormalGroupJetIntegrality

open JetSubstitutionLemmas

section Field

variable {K : Type} [Field K]

theorem subst_zero {τ : Type} (g : PowerSeries K) :
    PowerSeries.subst (0 : MvPowerSeries τ K) g =
      MvPowerSeries.C (PowerSeries.constantCoeff g) := by
  classical
  ext e
  rw [PowerSeries.coeff_subst PowerSeries.HasSubst.zero]
  rw [finsum_eq_single _ 0 (fun d hd => by simp [zero_pow hd])]
  by_cases he : e = 0 <;> simp [he, MvPowerSeries.coeff_C, MvPowerSeries.coeff_one]

theorem logDeriv {R : Subring K} {l linv : PowerSeries K} (h : IsLogPair l linv)
    (hF : FGInt R l linv) : IsOneUnit R (PowerSeries.derivative K l) := by
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have h10 : MvPowerSeries.pderiv K (1 : Fin 2) (MvPowerSeries.X (0 : Fin 2)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have hFc := Pts.constantCoeff_fadd h hX0 hX1
  have e1 := congrArg (MvPowerSeries.pderiv K (1 : Fin 2)) (Pts.l_fadd h hX0 hX1)
  rw [map_add, IntegralMvPolynomialLemmas.pderiv_subst _ hFc, IntegralMvPolynomialLemmas.pderiv_subst _ hX0, IntegralMvPolynomialLemmas.pderiv_subst _ hX1, h10,
    MvPowerSeries.pderiv_X_self, mul_zero, zero_add, mul_one] at e1
  have ha : ∀ s : Fin 2, IsPt R ((![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K) s) := by
    intro s
    fin_cases s
    · exact Pts.isPt_X
    · exact ⟨map_zero _, fun n => by simp⟩
  have ha0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff
      ((![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K) s) = 0 := fun s => (ha s).1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have e2 := congrArg (MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)) e1
  rw [MvPowerSeries.subst_mul hs, Pts.substMv_subst hFc ha0, Pts.substMv_subst hX1 ha0,
    ← Pts.fadd_eq_substMv h hX (map_zero _), Pts.fadd_zero h hX, MvPowerSeries.subst_X hs] at e2
  have e3 : (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K) 1 = 0 := rfl
  have e4 : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.derivative K l) =
      PowerSeries.derivative K l := PowerSeries.X_subst _
  rw [e3, subst_zero, cc_derivative_log h, map_one, e4] at e2
  have hG : IntMv R (MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      (MvPowerSeries.pderiv K (1 : Fin 2)
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))))) :=
    IntegralMvPolynomialLemmas.intMv_substMv (IntegralMvPolynomialLemmas.intMv_pderiv hF 1) ha
  have hG0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      (MvPowerSeries.pderiv K (1 : Fin 2)
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))))) = 1 := by
    have e5 := congrArg MvPowerSeries.constantCoeff e2
    have e6 : MvPowerSeries.constantCoeff (PowerSeries.derivative K l : MvPowerSeries Unit K) = 1 :=
      cc_derivative_log h
    rwa [map_mul, e6, one_mul, map_one] at e5
  refine ⟨cc_derivative_log h, intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_of_mul_eq_one hG hG0 ?_)⟩
  rw [mul_comm]
  exact e2

end Field

section CharZero

variable {K : Type} [Field K] [CharZero K] {R : Subring K}

theorem ph_fadd {σ : Type} {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {a b : MvPowerSeries σ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (fadd l linv a b) ph =
      PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l)
        (PowerSeries.subst linv ph) :=
  subst_ph_linv h ph (Pts.constantCoeff_add_l h ha hb)

theorem third {l linv ph : PowerSeries K} (hFr : Frame R l linv ph) (hF1 : F1 R l linv ph) :
    IntMv R (PowerSeries.subst
        (PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) l +
          PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) l +
          PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) l)
        ((PowerSeries.derivative K)^[3] (PowerSeries.subst linv ph)) *
      PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l) *
      PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l) *
      PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l)) := by
  have h := hFr.1
  have hX : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X _
  have hP : ∀ i : Fin 3, IsPt R (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) :=
    fun i => ⟨hX i, Pts.intMv_X i⟩
  have hz : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) l) = 0 :=
    fun i => Pts.constantCoeff_subst_l h (hX i)
  have hzz : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) l) = 0 :=
    fun i j => by rw [map_add, hz, hz, add_zero]
  have hzzz : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) l) = 0 := by
    rw [map_add, hzz, hz, add_zero]
  have h01 : MvPowerSeries.pderiv K (0 : Fin 3) (MvPowerSeries.X (1 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h02 : MvPowerSeries.pderiv K (0 : Fin 3) (MvPowerSeries.X (2 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h10 : MvPowerSeries.pderiv K (1 : Fin 3) (MvPowerSeries.X (0 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h12 : MvPowerSeries.pderiv K (1 : Fin 3) (MvPowerSeries.X (2 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h20 : MvPowerSeries.pderiv K (2 : Fin 3) (MvPowerSeries.X (0 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h21 : MvPowerSeries.pderiv K (2 : Fin 3) (MvPowerSeries.X (1 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have hT := hF1 (Fin 3) _ _ _ (hP 0) (hP 1) (hP 2)
  have hI := IntegralMvPolynomialLemmas.intMv_pderiv (IntegralMvPolynomialLemmas.intMv_pderiv (expIntegralDeriv' K R (Fin 3) _ hT 0) 1) 2
  unfold be0 at hI
  rw [ph_fadd h ph (Pts.constantCoeff_fadd h (hX 0) (hX 1)) (hX 2), Pts.l_fadd h (hX 0) (hX 1),
    ph_fadd h ph (hX 0) (hX 1), ph_fadd h ph (hX 0) (hX 2), ph_fadd h ph (hX 1) (hX 2)] at hI
  simp only [IntegralMvPolynomialLemmas.pderiv_subst _ hzzz, IntegralMvPolynomialLemmas.pderiv_subst _ (hzz _ _), IntegralMvPolynomialLemmas.pderiv_subst _ (hX _),
    map_add, map_sub, Derivation.leibniz, MvPowerSeries.pderiv_X_self, h01, h02, h10, h12, h20, h21,
    smul_eq_mul, mul_zero, mul_one, add_zero, zero_add, sub_zero, sub_self] at hI
  have e : (PowerSeries.derivative K)^[3] (PowerSeries.subst linv ph) =
      PowerSeries.derivative K (PowerSeries.derivative K (PowerSeries.derivative K
        (PowerSeries.subst linv ph))) := rfl
  rw [e]
  convert hI using 1
  ring

theorem integral_third_invariant_derivative {l linv ph : PowerSeries K} (hFr : Frame R l linv ph) (hF1 : F1 R l linv ph) :
    IntPS R ((Dinv l)^[3] ph) := by
  have h := hFr.1
  have hl := logDeriv h hFr.2.1
  have hX : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X _
  have hz : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) l) = 0 :=
    fun i => Pts.constantCoeff_subst_l h (hX i)
  have hzzz : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) l) = 0 := by
    rw [map_add, map_add, hz, hz, hz, add_zero, add_zero]
  have ha : ∀ s : Fin 3, IsPt R ((![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) s) := by
    intro s
    fin_cases s
    · exact Pts.isPt_X
    · exact ⟨map_zero _, fun n => by simp⟩
    · exact ⟨map_zero _, fun n => by simp⟩
  have ha0 : ∀ s : Fin 3, MvPowerSeries.constantCoeff
      ((![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) s) = 0 := fun s => (ha s).1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hI := IntegralMvPolynomialLemmas.intMv_substMv (third hFr hF1) ha
  have a0 : (![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) 0 = PowerSeries.X := rfl
  have a1 : (![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) 1 = 0 := rfl
  have a2 : (![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) 2 = 0 := rfl
  have eX : ∀ g : PowerSeries K, PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) g = g :=
    fun g => PowerSeries.X_subst g
  rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs,
    Pts.substMv_subst hzzz ha0, Pts.substMv_subst (hX 0) ha0, Pts.substMv_subst (hX 1) ha0,
    Pts.substMv_subst (hX 2) ha0, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    Pts.substMv_subst (hX 0) ha0, Pts.substMv_subst (hX 1) ha0, Pts.substMv_subst (hX 2) ha0,
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs, a0, a1, a2,
    subst_zero, subst_zero, cc_derivative_log h, h.1, map_zero, map_one, add_zero, add_zero,
    mul_one, mul_one, eX, eX, ← subst_Dinv_iterate h] at hI
  have hl0 : MvPowerSeries.constantCoeff (l : MvPowerSeries Unit K) = 0 := h.1
  rw [Pts.subst_subst h.2.2.1 hl0, h.2.2.2.1, eX] at hI
  have hne : PowerSeries.constantCoeff (PowerSeries.derivative K l) ≠ 0 := by
    rw [hl.1]; exact one_ne_zero
  have hinv : IntPS R (PowerSeries.derivative K l)⁻¹ :=
    intPS_of_mul_eq_one hl.2 hl.1 (PowerSeries.mul_inv_cancel _ hne)
  have e : (Dinv l)^[3] ph =
      ((Dinv l)^[3] ph * PowerSeries.derivative K l) * (PowerSeries.derivative K l)⁻¹ := by
    rw [mul_assoc, PowerSeries.mul_inv_cancel _ hne, mul_one]
  rw [e]
  exact intPS_mul (intPS_of_intMv hI) hinv

end CharZero

end FormalGroupJetIntegrality

open JetSubstitutionLemmas in
theorem log_derivative_integral' : LogDerivInt := by
  intro K iF iC R l linv h hF
  exact FormalGroupJetIntegrality.logDeriv h hF

open JetSubstitutionLemmas in
theorem third_jet_integral : ThirdJetIntegral := by
  intro K _ _ R l linv ph hFr hF1
  have hl := FormalGroupJetIntegrality.logDeriv hFr.1 hFr.2.1
  have key : ∀ j : ℕ, IntPS R ((Dinv l)^[j + 3] ph) := by
    intro j
    induction j with
    | zero => exact FormalGroupJetIntegrality.integral_third_invariant_derivative hFr hF1
    | succ j ih =>
      rw [show j + 1 + 3 = (j + 3) + 1 by ring, Function.iterate_succ_apply']
      exact intPS_Dinv hl (intPS_derivative ih)
  refine ⟨key 0, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩
  unfold jet
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact key j 0

theorem jets_unramified : JetsUnramified := by
  intro K _ _ R l linv ph a b hFr hF1 hN h2 hAdj hinv hab
  have hl := FormalGroupJetIntegrality.logDeriv hFr.1 hFr.2.1
  have hj : ∀ i : ℕ, 1 ≤ i → jet l ph i ∈ R := by
    intro i hi
    rcases (by omega : i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | h3
    · exact jetOne' K R l linv ph hFr.1 hl hFr.2.2 hN h2
    · have e := R.mul_mem hinv (jetAdjoint' K R l linv ph a b hFr.1 hFr.2.2 hAdj)
      rwa [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hab), one_mul] at e
    · exact (third_jet_integral K R l linv ph hFr hF1).2 i h3
  exact ⟨hj, jetExp' K R l linv ph hFr.1 hFr.2.2 hj⟩

theorem jets_shape : JetsShape := by
  intro K _ _ R l linv ph hFr hF1 hN h2
  have hl := FormalGroupJetIntegrality.logDeriv hFr.1 hFr.2.1
  refine ⟨jetExpShape' K R l linv ph hFr.1 hFr.2.2 (fun i hi hi2 => ?_),
    fun a b hAdj => jetAdjoint' K R l linv ph a b hFr.1 hFr.2.2 hAdj⟩
  rcases (by omega : i = 1 ∨ 3 ≤ i) with rfl | h3
  · exact jetOne' K R l linv ph hFr.1 hl hFr.2.2 hN h2
  · exact (third_jet_integral K R l linv ph hFr hF1).2 i h3

theorem sum_two_units_product : SumTwoUnitsProd := by
  intro A B _ _ hA hB x
  obtain ⟨u1, v1, h1⟩ := hA x.1
  obtain ⟨u2, v2, h2⟩ := hB x.2
  exact ⟨MulEquiv.prodUnits.symm (u1, u2), MulEquiv.prodUnits.symm (v1, v2), Prod.ext h1 h2⟩

end Formalism.L2.Th1.C
