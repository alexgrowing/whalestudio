import Formalism.LocalToGlobal.InertKernelTheory.KerTransAll
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgTrans
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.PDeriv
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open scoped ComplexConjugate Topology

def PTorsAlg (L : PeriodPair) : Prop :=
  ∀ u : ℂ, (∃ N : ℕ, 0 < N ∧ (N : ℂ) * u ∈ L.lattice) → u ∉ L.lattice →
    L.weierstrassP u ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ L.derivWeierstrassP u ∈ Formalism.MainNotions.TaylorLogMetric.Qbar

def KleinAlg (L : PeriodPair) (ω₀ : ℂ) : Prop :=
  ∀ s : ℂ, (∃ N : ℕ, 0 < N ∧ (N : ℂ) * s ∈ L.lattice) →
    Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) 0 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧
      deriv (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) 0 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar

def PTorsAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → PTorsAlg B.L

def KleinAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → KleinAlg B.L B.ω₀

namespace AlgP

section Rec

variable (M : IntermediateField ℚ ℂ)

theorem mem_of_mul_mem {x a : ℂ} (ha : a ∈ M) (ha0 : a ≠ 0) (h : x * a ∈ M) : x ∈ M := by
  have := div_mem h ha
  rwa [mul_div_cancel_right₀ _ ha0] at this

theorem succ_mem (m : ℕ) : ((m : ℂ) + 1) ∈ M := add_mem (natCast_mem M m) (one_mem M)

theorem succ_ne (m : ℕ) : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast m.succ_ne_zero

theorem rec1 (P V : PowerSeries ℂ) (h : PowerSeries.derivative ℂ P = V * P)
    (hV : ∀ k, PowerSeries.coeff k V ∈ M) (h0 : PowerSeries.coeff 0 P ∈ M) : ∀ n, PowerSeries.coeff n P ∈ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact h0
    | succ m =>
      have e := congrArg (PowerSeries.coeff m) h
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at e
      refine mem_of_mul_mem M (succ_mem M m) (succ_ne m) ?_
      rw [e]
      refine sum_mem fun p hp => mul_mem (hV _) (ih _ ?_)
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      omega

theorem rec0 (V Q : PowerSeries ℂ) (h : PowerSeries.derivative ℂ V = Q)
    (hQ : ∀ k, PowerSeries.coeff k Q ∈ M) (h0 : PowerSeries.coeff 0 V ∈ M) : ∀ n, PowerSeries.coeff n V ∈ M := by
  intro n
  cases n with
  | zero => exact h0
  | succ m =>
    have e := congrArg (PowerSeries.coeff m) h
    rw [PowerSeries.coeff_derivative] at e
    refine mem_of_mul_mem M (succ_mem M m) (succ_ne m) ?_
    rw [e]
    exact hQ m

theorem rec2 (W : PowerSeries ℂ) (c : ℂ) (hc : c ∈ M)
    (h : PowerSeries.derivative ℂ (PowerSeries.derivative ℂ W) = PowerSeries.C (6 : ℂ) * (W * W) + PowerSeries.C c)
    (h0 : PowerSeries.coeff 0 W ∈ M) (h1 : PowerSeries.coeff 1 W ∈ M) : ∀ n, PowerSeries.coeff n W ∈ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | m + 2, ih =>
      have e := congrArg (PowerSeries.coeff m) h
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, map_add, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mul, PowerSeries.coeff_C] at e
      have h6 : (6 : ℂ) ∈ M := by
        have := natCast_mem M 6
        simpa using this
      have hsum : PowerSeries.coeff (m + 1 + 1) W * ((((m + 1 : ℕ) : ℂ)) + 1) * ((m : ℂ) + 1) ∈ M := by
        rw [e]
        refine add_mem (mul_mem h6 (sum_mem fun p hp => mul_mem (ih _ ?_) (ih _ ?_))) ?_
        · have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
          omega
        · have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
          omega
        · split_ifs
          · exact hc
          · exact zero_mem _
      exact mem_of_mul_mem M (succ_mem M (m + 1)) (succ_ne (m + 1))
        (mem_of_mul_mem M (succ_mem M m) (succ_ne m) hsum)

end Rec

section OneVarK

open Formalism.L2.Th1.F

theorem coeff0_taylor0 (f : ℂ → ℂ) : PowerSeries.coeff 0 (taylor0 f) = f 0 := by
  rw [Taylor.coeff_taylor0]
  simp

theorem coeff1_taylor0 (f : ℂ → ℂ) : PowerSeries.coeff 1 (taylor0 f) = deriv f 0 := by
  rw [Taylor.coeff_taylor0]
  simp

theorem analyticAt_of_eventually {f : ℂ → ℂ} (h : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ f z) : AnalyticAt ℂ f 0 :=
  DifferentiableOn.analyticAt (fun z hz => DifferentiableAt.differentiableWithinAt hz) h

theorem caseA (L : PeriodPair) (ω₀ s : ℂ) (hω : ω₀ ∈ L.lattice) (hh : ω₀ / 2 ∉ L.lattice)
    (hu : s + ω₀ / 2 ∉ L.lattice) (M : IntermediateField ℚ ℂ) (h2 : L.g₂ ∈ M) (hs2 : s2 L ∈ M)
    (hp : L.weierstrassP (s + ω₀ / 2) ∈ M) (hp' : L.derivWeierstrassP (s + ω₀ / 2) ∈ M)
    (hg0 : opU L s (th0 L (ω₀ / 2)) 0 ∈ M) (hd0 : deriv (opU L s (th0 L (ω₀ / 2))) 0 ∈ M) :
    CoefIn1 (opU L s (th0 L (ω₀ / 2))) M := by
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), z + (s + ω₀ / 2) ∉ L.lattice := by
    have h1 := PDeriv.eventually_notMem L hu
    have h2 : Filter.Tendsto (fun z : ℂ => z + (s + ω₀ / 2)) (𝓝 0) (𝓝 (s + ω₀ / 2)) :=
      (continuous_add_const (s + ω₀ / 2)).tendsto' 0 _ (by simp)
    exact h2.eventually h1
  have hthd : Differentiable ℂ (th0 L (ω₀ / 2)) := (th0Basic L ω₀ hω hh).1
  let v : ℂ → ℂ := fun z => wZeta L (z + (s + ω₀ / 2)) - wZeta L (ω₀ / 2) - s2 L * (z + s)
    - (Real.pi : ℂ) * (conj s / (area L : ℂ))
  let w : ℂ → ℂ := fun z => L.weierstrassP (z + (s + ω₀ / 2))
  have eg : opU L s (th0 L (ω₀ / 2)) = fun y => th0 L (ω₀ / 2) (y + s) *
      Complex.exp (-(Real.pi : ℂ) * herm L y s - (Real.pi : ℂ) * herm L s s / 2) := rfl

  have hG : ∀ z, z + (s + ω₀ / 2) ∉ L.lattice →
      HasDerivAt (opU L s (th0 L (ω₀ / 2))) (v z * opU L s (th0 L (ω₀ / 2)) z) z := by
    intro z hz
    have hz' : z + s + ω₀ / 2 ∉ L.lattice := by rwa [add_assoc]
    have h1 : HasDerivAt (fun y => th0 L (ω₀ / 2) (y + s))
        ((wZeta L (z + s + ω₀ / 2) - wZeta L (ω₀ / 2) - s2 L * (z + s)) * th0 L (ω₀ / 2) (z + s)) z :=
      (th0LogDeriv L ω₀ (z + s) hω hh hz').comp_add_const z s
    have h2 : HasDerivAt (fun y : ℂ => -(Real.pi : ℂ) * herm L y s - (Real.pi : ℂ) * herm L s s / 2)
        (-(Real.pi : ℂ) * (1 * conj s / (area L : ℂ))) z := by
      unfold herm
      exact ((((hasDerivAt_id z).mul_const (conj s)).div_const (area L : ℂ)).const_mul (-(Real.pi : ℂ))).sub_const _
    have h3 := h1.mul h2.cexp
    rw [eg]
    refine h3.congr_deriv ?_
    simp only [v]
    rw [show z + (s + ω₀ / 2) = z + s + ω₀ / 2 by ring]
    ring
  have hV : ∀ z, z + (s + ω₀ / 2) ∉ L.lattice →
      HasDerivAt v (-(L.weierstrassP (z + (s + ω₀ / 2))) - s2 L * 1 - 0) z := by
    intro z hz
    have h1 := (zetaHasDeriv L (z + (s + ω₀ / 2)) hz).comp_add_const z (s + ω₀ / 2)
    have h2 := ((hasDerivAt_id z).add_const s).const_mul (s2 L)
    exact ((h1.sub_const (wZeta L (ω₀ / 2))).sub h2).sub (hasDerivAt_const z _)
  have hW : ∀ z, z + (s + ω₀ / 2) ∉ L.lattice → HasDerivAt w (L.derivWeierstrassP (z + (s + ω₀ / 2))) z :=
    fun z hz => (PDeriv.hasDerivAt_P L hz).comp_add_const z (s + ω₀ / 2)
  have hW2 : ∀ z, z + (s + ω₀ / 2) ∉ L.lattice →
      HasDerivAt (fun y => L.derivWeierstrassP (y + (s + ω₀ / 2)))
        (6 * L.weierstrassP (z + (s + ω₀ / 2)) ^ 2 - L.g₂ / 2) z :=
    fun z hz => (pSecond L (z + (s + ω₀ / 2)) hz).comp_add_const z (s + ω₀ / 2)

  have hgA : AnalyticAt ℂ (opU L s (th0 L (ω₀ / 2))) 0 := translation_operator_analytic L s hthd 0 (Set.mem_univ _)
  have hvA : AnalyticAt ℂ v 0 := analyticAt_of_eventually (hev.mono fun z hz => (hV z hz).differentiableAt)
  have hwA : AnalyticAt ℂ w 0 := analyticAt_of_eventually (hev.mono fun z hz => (hW z hz).differentiableAt)

  have TG : PowerSeries.derivative ℂ (taylor0 (opU L s (th0 L (ω₀ / 2)))) =
      taylor0 v * taylor0 (opU L s (th0 L (ω₀ / 2))) := by
    rw [← Taylor.taylor0_deriv, ← Taylor.taylor0_mul hvA hgA]
    exact Taylor.taylor0_congr (hev.mono fun z hz => (hG z hz).deriv)
  have TV : PowerSeries.derivative ℂ (taylor0 v) = PowerSeries.C (-1 : ℂ) * taylor0 w + PowerSeries.C (-(s2 L)) := by
    rw [← Taylor.taylor0_deriv]
    have e1 := Taylor.taylor0_add (f := fun z => (-1 : ℂ) * w z) (g := fun _ => -(s2 L))
      (analyticAt_const.mul hwA) analyticAt_const
    rw [Taylor.taylor0_mul analyticAt_const hwA, Taylor.taylor0_const, Taylor.taylor0_const] at e1
    rw [← e1]
    refine Taylor.taylor0_congr (hev.mono fun z hz => ?_)
    rw [(hV z hz).deriv]
    simp only [w]
    ring
  have hdw : ∀ᶠ z in 𝓝 (0 : ℂ), deriv w z = L.derivWeierstrassP (z + (s + ω₀ / 2)) :=
    hev.mono fun z hz => (hW z hz).deriv
  have hdw' : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ᶠ y in 𝓝 z, deriv w y = L.derivWeierstrassP (y + (s + ω₀ / 2)) :=
    hdw.eventually_nhds
  have TW : PowerSeries.derivative ℂ (PowerSeries.derivative ℂ (taylor0 w)) =
      PowerSeries.C (6 : ℂ) * (taylor0 w * taylor0 w) + PowerSeries.C (-(L.g₂ / 2)) := by
    rw [← Taylor.taylor0_deriv, ← Taylor.taylor0_deriv]
    have e1 := Taylor.taylor0_add (f := fun z => (6 : ℂ) * (w z * w z)) (g := fun _ => -(L.g₂ / 2))
      (analyticAt_const.mul (hwA.mul hwA)) analyticAt_const
    rw [Taylor.taylor0_mul (f := fun _ => (6 : ℂ)) (g := fun z => w z * w z) analyticAt_const (hwA.mul hwA),
      Taylor.taylor0_mul hwA hwA, Taylor.taylor0_const, Taylor.taylor0_const] at e1
    rw [← e1]
    refine Taylor.taylor0_congr ((hev.and hdw').mono fun z hz => ?_)
    rw [Filter.EventuallyEq.deriv_eq hz.2, (hW2 z hz.1).deriv]
    simp only [w]
    ring

  have hu0 : (0 : ℂ) + (s + ω₀ / 2) ∉ L.lattice := by rwa [zero_add]
  have hg0ne : opU L s (th0 L (ω₀ / 2)) 0 ≠ 0 := by
    rw [eg]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    intro h0
    apply hu
    have := ((th0Basic L ω₀ hω hh).2.2.2.1 (0 + s)).1 h0
    rwa [zero_add] at this
  have hv0 : v 0 ∈ M := by
    have e := (hG 0 hu0).deriv
    have : v 0 = deriv (opU L s (th0 L (ω₀ / 2))) 0 / opU L s (th0 L (ω₀ / 2)) 0 := by
      rw [e, mul_div_cancel_right₀ _ hg0ne]
    rw [this]
    exact div_mem hd0 hg0
  have hWc : ∀ n, PowerSeries.coeff n (taylor0 w) ∈ M := by
    refine rec2 M _ _ (neg_mem (div_mem h2 ?_)) TW ?_ ?_
    · have := natCast_mem M 2
      simpa using this
    · rw [coeff0_taylor0]
      simp only [w, zero_add]
      exact hp
    · rw [coeff1_taylor0, (hW 0 hu0).deriv, zero_add]
      exact hp'
  have hVc : ∀ n, PowerSeries.coeff n (taylor0 v) ∈ M := by
    refine rec0 M _ _ TV ?_ ?_
    · intro k
      rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C]
      refine add_mem (mul_mem (neg_mem (one_mem _)) (hWc k)) ?_
      split_ifs
      · exact neg_mem hs2
      · exact zero_mem _
    · rw [coeff0_taylor0]
      exact hv0
  intro k
  refine rec1 M _ _ TG hVc ?_ k
  rw [coeff0_taylor0]
  exact hg0

theorem caseB (L : PeriodPair) (ω₀ s : ℂ) (hu : s + ω₀ / 2 ∈ L.lattice) (M : IntermediateField ℚ ℂ)
    (h2 : L.g₂ ∈ M) (h3 : L.g₃ ∈ M) (hs2 : s2 L ∈ M) (hd0 : deriv (opU L s (th0 L (ω₀ / 2))) 0 ∈ M) :
    CoefIn1 (opU L s (th0 L (ω₀ / 2))) M := by
  have hψ : semiChar L (s + ω₀ / 2) ≠ 0 := by
    unfold semiChar
    split_ifs <;> norm_num
  set K : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L s (ω₀ / 2) : ℂ)) / semiChar L (s + ω₀ / 2)
    / opU L (ω₀ / 2) (sgStar L) 0 with hK
  have eg : opU L s (th0 L (ω₀ / 2)) = fun z => K * sgStar L z := by
    funext z
    rw [opUTh0 L (ω₀ / 2) s z]
    have hf := sgStarFixed L (s + ω₀ / 2) z hu
    have e : opU L (s + ω₀ / 2) (sgStar L) z = sgStar L z / semiChar L (s + ω₀ / 2) := by
      rw [← hf, mul_div_cancel_left₀ _ hψ]
    rw [e, hK]
    ring
  have hsd := sgStarBasic L
  have hK0 : K ∈ M := by
    have e : deriv (opU L s (th0 L (ω₀ / 2))) 0 = K := by
      rw [eg, deriv_const_mul _ (hsd.1 0), hsd.2.2.2.1, mul_one]
    rw [← e]
    exact hd0
  let j : M →+* ℂ := algebraMap M ℂ
  let PM : PowerSeries M := Formalism.L2.Th1.F.pOf (⟨L.g₂, h2⟩ : M) ⟨L.g₃, h3⟩
  have hS : taylor0 (sgStar L) = PowerSeries.map j (Formalism.L2.Th1.B.sgStar (⟨s2 L, hs2⟩ : M) PM) := by
    rw [taylorSgStar L, Formalism.L2.Th1.B.Map.map_sgStar, ← pSeries_eq_map M L h2 h3]
    rfl
  have hsA : AnalyticAt ℂ (sgStar L) 0 := (hsd.1).analyticAt 0
  intro k
  rw [eg, Taylor.taylor0_mul analyticAt_const hsA, Taylor.taylor0_const, PowerSeries.coeff_C_mul, hS,
    PowerSeries.coeff_map]
  exact mul_mem hK0 (PowerSeries.coeff k (Formalism.L2.Th1.B.sgStar (⟨s2 L, hs2⟩ : M) PM)).2

theorem th0TransAlg_of (L : PeriodPair) (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) (hh : ω₀ / 2 ∉ L.lattice)
    (hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hs2 : s2 L ∈ Formalism.MainNotions.TaylorLogMetric.Qbar)
    (hP : PTorsAlg L) (hK : KleinAlg L ω₀) : PeriodPairTranscendence L ω₀ := by
  intro s hs
  obtain ⟨hk0, hk1⟩ := hK s hs
  by_cases hu : s + ω₀ / 2 ∈ L.lattice
  · obtain ⟨M, hMf, hM⟩ := exists_nf {L.g₂, L.g₃, s2 L, deriv (opU L s (th0 L (ω₀ / 2))) 0} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    exact ⟨M, hMf, caseB L ω₀ s hu M (hM _ (by simp)) (hM _ (by simp)) (hM _ (by simp)) (hM _ (by simp))⟩
  · obtain ⟨N, hN, hNs⟩ := hs
    have htor : ∃ N' : ℕ, 0 < N' ∧ (N' : ℂ) * (s + ω₀ / 2) ∈ L.lattice := by
      refine ⟨2 * N, by omega, ?_⟩
      have e : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) = (N : ℂ) * s + (N : ℂ) * s + N • ω₀ := by
        rw [nsmul_eq_mul]
        push_cast
        ring
      rw [e]
      exact add_mem (add_mem hNs hNs) (nsmul_mem hω N)
    obtain ⟨hp, hp'⟩ := hP _ htor hu
    obtain ⟨M, hMf, hM⟩ := exists_nf {L.g₂, s2 L, L.weierstrassP (s + ω₀ / 2), L.derivWeierstrassP (s + ω₀ / 2),
      opU L s (th0 L (ω₀ / 2)) 0, deriv (opU L s (th0 L (ω₀ / 2))) 0} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    exact ⟨M, hMf, caseA L ω₀ s hω hh hu M (hM _ (by simp)) (hM _ (by simp)) (hM _ (by simp)) (hM _ (by simp))
      (hM _ (by simp)) (hM _ (by simp))⟩

end OneVarK

section AllK

theorem th0TransAll_of (hP : PTorsAll) (hK : KleinAll) : PeriodTranscendenceAllLattices := by
  intro D cc δ B hcc hδ
  have sd : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  obtain ⟨h2, h3⟩ := Sigma.invAlg' D cc δ hcc hδ B.L B.lat
  exact th0TransAlg_of B.L B.ω₀ sd.per sd.half h2 h3 (Sigma.secondEisensteinAlgebraic D cc δ hcc hδ B.L B.lat)
    (hP D cc δ B hcc hδ) (hK D cc δ B hcc hδ)

theorem pTorsAlg_of (L : PeriodPair) (hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : PTorsAlg L := by
  rintro u ⟨N, hN, hNu⟩ hu
  haveI : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  have hx : IsAlgebraic ℚ (L.weierstrassP u) :=
    (PI.GalTorsConj.W.wp_isAlgebraic L Formalism.MainNotions.TaylorLogMetric.Qbar hg2 hg3 N u hN hNu hu).restrictScalars ℚ
  have hsq : L.derivWeierstrassP u ^ 2 = 4 * L.weierstrassP u ^ 3 - L.g₂ * L.weierstrassP u - L.g₃ := by
    have e := L.derivWeierstrassP_sq u hu
    linear_combination e
  exact ⟨mem_algebraicClosure_iff.2 hx, mem_algebraicClosure_iff.2
    (PI.GalTorsConj.W.alg_of_sq hsq hx (mem_algebraicClosure_iff.1 hg2) (mem_algebraicClosure_iff.1 hg3))⟩

theorem torsion_points_algebraic : PTorsAll := fun D cc δ B hcc hδ =>
  pTorsAlg_of B.L (Sigma.invAlg' D cc δ hcc hδ B.L B.lat).1 (Sigma.invAlg' D cc δ hcc hδ B.L B.lat).2

theorem kerTransAll_of_klein (hP : PTorsAll) (hK : KleinAll) : KerTransAll :=
  kerTransAll_of (th0TransAll_of hP hK)

theorem kerTransAll_of_kleinAll (hK : KleinAll) : KerTransAll :=
  kerTransAll_of_klein torsion_points_algebraic hK

end AllK

end AlgP

end Formalism.L2.KerInert
