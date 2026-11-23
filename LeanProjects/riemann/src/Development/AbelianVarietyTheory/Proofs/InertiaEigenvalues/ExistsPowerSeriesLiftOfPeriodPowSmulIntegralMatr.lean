import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.KisinFF

theorem exists_of_inclW_eq_pow_mul {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → ∃ a', a = (l : Ainf l) ^ n * a' ∧ inclW l a' = w := by
  induction n with
  | zero => intro a w h; exact ⟨a, by simp, by simpa using h⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨a', ha', hw'⟩ := ih a₁ w ha₁
    refine ⟨a', ?_, hw'⟩
    have h1 : a = (l : Ainf l) * a₁ := by
      apply GlobalTheory.HWL.TensorWitt.inclW_injective
      rw [map_mul, map_natCast, ha₁, h]; ring
    rw [h1, ha']; ring

theorem scalar {l : ℕ} [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (M : ℕ)
    (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : inclW l a = inclW l τ ^ M * w) :
    ∃ s : bk.S, bk.evW s = w := by
  classical
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB M
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  obtain ⟨v, -, hv⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : bk.S, s₀ = c.sum fun i μ => μ * TB.c i a := ⟨_, rfl⟩
  have hev : ∀ t : bk.S, inclW l (bk.ev t) = bk.evW t := fun t => rfl
  have key : ∀ n : ℕ, (l : WCb l) ^ n ∣ bk.evW s₀ - (l : WCb l) ^ r * w := by
    intro n
    obtain ⟨m, s, y, h⟩ := hw n
    have hz : inclW l (bk.ev X ^ m * a - τ ^ M * bk.ev s) = (l : WCb l) ^ n * (inclW l τ ^ M * y) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, hev, hev, ha]
      linear_combination (inclW l τ ^ M) * h
    obtain ⟨z', hz', -⟩ := exists_of_inclW_eq_pow_mul n _ _ hz
    have hci : ∀ i, X ^ m * TB.c i a - s * TB.c i (τ ^ M) = (l : bk.S) ^ n * TB.c i z' := by
      intro i
      have := congrArg (TB.c i) hz'
      rw [map_sub, show bk.ev X ^ m = bk.ev (X ^ m) from (map_pow _ _ _).symm, TB.c_mul, mul_comm (τ ^ M) (bk.ev s), TB.c_mul,
        show ((l : Ainf l) ^ n) = bk.ev ((l : bk.S) ^ n) by simp, TB.c_mul] at this
      exact this
    obtain ⟨t, ht⟩ : ∃ t : bk.S, t = c.sum fun i μ => μ * TB.c i z' := ⟨_, rfl⟩
    have hS : X ^ m * s₀ - s * (l : bk.S) ^ r = (l : bk.S) ^ n * t := by
      rw [← hc, hs₀, ht]
      simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by linear_combination c i * hci i
    have hW := congrArg bk.evW hS
    simp only [map_sub, map_mul, map_pow, map_natCast] at hW
    have hv' : bk.evW X ^ m * v ^ m = 1 := by rw [← mul_pow, hv, one_pow]
    refine ⟨v ^ m * (bk.evW t - (l : WCb l) ^ r * y), ?_⟩
    linear_combination v ^ m * hW - (l : WCb l) ^ r * v ^ m * h - (bk.evW s₀ - (l : WCb l) ^ r * w) * hv'
  have hd : bk.evW s₀ - (l : WCb l) ^ r * w = 0 := by
    refine IsHausdorff.haus' (I := Ideal.span {(l : WCb l)}) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact key n
  obtain ⟨a', -, ha'⟩ := exists_of_inclW_eq_pow_mul r (bk.ev s₀) w (by rw [hev]; linear_combination hd)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.integral_witt_element_of_evaluation l K bk w hw a' ha'.symm
  exact ⟨s', by rw [← hev, ← hs', ha']⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  intro l _ K bk τ hτ d d' M X x hX hx
  have he : ∀ i j, inclW l (x i j) = inclW l τ ^ M * X i j := fun i j => by
    have := congrFun (congrFun hx i) j
    simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
  choose Y hY using fun i j => scalar K bk τ hτ M (X i j) (hX i j) (x i j) (he i j)
  exact ⟨Y, Matrix.ext fun i j => hY i j⟩

end GlobalTheory.BSP.KisinFF
