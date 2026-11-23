import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.Curves

noncomputable section

open Finset Matrix MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.RgStepFam

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem mul_inUJ {a b : Matrix (Fin n) (Fin n) ℂ} (ha : Formalism.REAL.inUJ ε a) (hb : Formalism.REAL.inUJ ε b) :
    Formalism.REAL.inUJ ε (a * b) := by
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha, hb]

theorem inv_mul_of_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) : g⁻¹ * g = 1 := by
  have h : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    unfold Formalism.REAL.inUJ at hg
    calc (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Formalism.REAL.Jm_mul_self]
  rw [Matrix.inv_eq_left_inv h]
  exact h

theorem exp_hasSum (X : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • X ^ k) (NormedSpace.exp X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X

theorem exp_mul_eig (A P : Matrix (Fin n) (Fin n) ℂ) (lam τ : ℂ) (h : A * P = lam • P) :
    NormedSpace.exp (τ • A) * P = Complex.exp (τ * lam) • P := by
  have hp : ∀ k : ℕ, (τ • A) ^ k * P = (τ * lam) ^ k • P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, smul_mul_assoc, h, smul_smul, smul_smul, pow_succ']
      congr 1
      ring
  have h1 := (exp_hasSum (τ • A)).mul_right P
  have h2 : HasSum (fun k : ℕ => (((k.factorial : ℂ)⁻¹) • (τ * lam) ^ k) • P) (Complex.exp (τ * lam) • P) := by
    have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (τ * lam)
    rw [← Complex.exp_eq_exp_ℂ] at h3
    exact h3.smul_const P
  refine h1.unique (h2.congr_fun ?_ )
  intro k
  rw [smul_mul_assoc, hp, smul_assoc]

theorem exp_three {A : Matrix (Fin n) (Fin n) ℂ} (hA : A * A * A = A) (τ : ℂ) :
    NormedSpace.exp (τ • A) = Complex.exp τ • ((1 / 2 : ℂ) • (A * A + A)) +
      Complex.exp (-τ) • ((1 / 2 : ℂ) • (A * A - A)) + (1 - A * A) := by
  have hA' : A * (A * A) = A := by rw [← mul_assoc, hA]
  have e1 : A * ((1 / 2 : ℂ) • (A * A + A)) = (1 : ℂ) • ((1 / 2 : ℂ) • (A * A + A)) := by
    rw [mul_smul_comm, mul_add, hA', one_smul]
    congr 1
    exact add_comm _ _
  have e2 : A * ((1 / 2 : ℂ) • (A * A - A)) = (-1 : ℂ) • ((1 / 2 : ℂ) • (A * A - A)) := by
    rw [mul_smul_comm, mul_sub, hA']
    module
  have e3 : A * (1 - A * A) = (0 : ℂ) • (1 - A * A) := by
    rw [mul_sub, hA', mul_one, sub_self, zero_smul]
  have hs : (1 / 2 : ℂ) • (A * A + A) + (1 / 2 : ℂ) • (A * A - A) + (1 - A * A) = 1 := by
    module
  calc NormedSpace.exp (τ • A) = NormedSpace.exp (τ • A) *
        ((1 / 2 : ℂ) • (A * A + A) + (1 / 2 : ℂ) • (A * A - A) + (1 - A * A)) := by rw [hs, mul_one]
    _ = _ := by
      rw [mul_add, mul_add, exp_mul_eig A _ 1 τ e1, exp_mul_eig A _ (-1) τ e2, exp_mul_eig A _ 0 τ e3]
      simp

theorem exp_entry_bound {A : Matrix (Fin n) (Fin n) ℂ} (hA : A * A * A = A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ i j,
      ‖NormedSpace.exp ((t : ℂ) • A) i j‖ ≤ C * Real.exp t ∧
      ‖NormedSpace.exp (-((t : ℂ) • A)) i j‖ ≤ C * Real.exp t := by
  set P : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A) with hP
  set Q : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A) with hQ
  set R : Matrix (Fin n) (Fin n) ℂ := 1 - A * A with hR
  have hnn : ∀ i j, 0 ≤ ‖P i j‖ + ‖Q i j‖ + ‖R i j‖ := fun i j => by positivity
  have hle : ∀ i j, ‖P i j‖ + ‖Q i j‖ + ‖R i j‖ ≤ ∑ a, ∑ b, (‖P a b‖ + ‖Q a b‖ + ‖R a b‖) := fun i j =>
    (single_le_sum (f := fun b => ‖P i b‖ + ‖Q i b‖ + ‖R i b‖) (fun b _ => hnn i b) (mem_univ j)).trans
      (single_le_sum (f := fun a => ∑ b, (‖P a b‖ + ‖Q a b‖ + ‖R a b‖))
        (fun a _ => sum_nonneg fun b _ => hnn a b) (mem_univ i))
  have key : ∀ (τ : ℂ) (t : ℝ), 0 ≤ t → ‖Complex.exp τ‖ ≤ Real.exp t → ‖Complex.exp (-τ)‖ ≤ Real.exp t → ∀ i j,
      ‖NormedSpace.exp (τ • A) i j‖ ≤ (∑ a, ∑ b, (‖P a b‖ + ‖Q a b‖ + ‖R a b‖)) * Real.exp t := by
    intro τ t ht h1 h2 i j
    have h3 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
    rw [exp_three hA τ]
    have e : (Complex.exp τ • P + Complex.exp (-τ) • Q + R) i j =
        Complex.exp τ * P i j + Complex.exp (-τ) * Q i j + R i j := by simp
    rw [e]
    calc _ ≤ ‖Complex.exp τ * P i j‖ + ‖Complex.exp (-τ) * Q i j‖ + ‖R i j‖ := norm_add₃_le
      _ ≤ Real.exp t * ‖P i j‖ + Real.exp t * ‖Q i j‖ + Real.exp t * ‖R i j‖ := by
        rw [norm_mul, norm_mul]
        gcongr
        nlinarith [norm_nonneg (R i j)]
      _ = (‖P i j‖ + ‖Q i j‖ + ‖R i j‖) * Real.exp t := by ring
      _ ≤ _ := by gcongr; exact hle i j
  refine ⟨∑ a, ∑ b, (‖P a b‖ + ‖Q a b‖ + ‖R a b‖), sum_nonneg fun a _ => sum_nonneg fun b _ => hnn a b,
    fun t ht i j => ⟨?_, ?_⟩⟩
  · refine key _ t ht ?_ ?_ i j
    · rw [Complex.norm_exp]; simp
    · rw [Complex.norm_exp]; simp [ht]
  · rw [← neg_smul]
    refine key _ t ht ?_ ?_ i j
    · rw [Complex.norm_exp]; simp [ht]
    · rw [Complex.norm_exp]; simp

theorem mul_entry_le (x y : Matrix (Fin n) (Fin n) ℂ) {B : ℝ} (hy : ∀ i j, ‖y i j‖ ≤ B) (j k : Fin n) :
    ‖(x * y) j k‖ ≤ (∑ a, ∑ b, ‖x a b‖) * B := by
  rw [Matrix.mul_apply]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hy j k)
  calc _ ≤ ∑ l, ‖x j l‖ * B := (norm_sum_le _ _).trans (sum_le_sum fun l _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hy l k) (norm_nonneg _))
    _ = (∑ l, ‖x j l‖) * B := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (single_le_sum (f := fun a => ∑ b, ‖x a b‖) (fun a _ => sum_nonneg fun b _ => norm_nonneg _) (mem_univ j)) hB

theorem mul_entry_le' (x y : Matrix (Fin n) (Fin n) ℂ) {B : ℝ} (hy : ∀ i j, ‖y i j‖ ≤ B) (j k : Fin n) :
    ‖(y * x) j k‖ ≤ (∑ a, ∑ b, ‖x a b‖) * B := by
  rw [Matrix.mul_apply]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hy j k)
  calc _ ≤ ∑ l, ‖x l k‖ * B := (norm_sum_le _ _).trans (sum_le_sum fun l _ => by
        rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (hy j l) (norm_nonneg _))
    _ = (∑ l, ‖x l k‖) * B := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_le_sum fun l _ => single_le_sum (f := fun b => ‖x l b‖) (fun b _ => norm_nonneg _) (mem_univ k)) hB

theorem lint_lt_top {f : ℝ → ℂ} {h w : Fin n → ℝ → ℂ} {C s : ℝ}
    (hf : ∀ t, 0 < t → f t = ∑ k, w k t * h k t) (hw : ∀ k t, 0 < t → ‖w k t‖ ≤ C * Real.exp t)
    (hh : ∀ k, Continuous (h k))
    (hfin : ∀ k, ∫⁻ t in Set.Ioi (0 : ℝ), ‖h k t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * (s - 1) * t)) < ⊤) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t)) < ⊤ := by
  set G : Fin n → ℝ → ℝ≥0∞ := fun k t => ‖h k t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * (s - 1) * t)) with hG
  have hmeas : ∀ k, Measurable (G k) := fun k =>
    (((hh k).measurable.enorm).pow_const 2).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t)) ≤
      ENNReal.ofReal ((n : ℝ) * C ^ 2) * ∑ k, G k t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : ‖f t‖ ^ 2 * Real.exp (-2 * s * t) ≤
        (n : ℝ) * C ^ 2 * ∑ k, ‖h k t‖ ^ 2 * Real.exp (-2 * (s - 1) * t) := by
      have h2 : ‖f t‖ ≤ ∑ k, C * Real.exp t * ‖h k t‖ := by
        rw [hf t ht']
        refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hw k t ht') (norm_nonneg _)
      have h3 : ‖f t‖ ^ 2 ≤ (n : ℝ) * ∑ k, (C * Real.exp t * ‖h k t‖) ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := fun k => C * Real.exp t * ‖h k t‖)
        simp only [card_univ, Fintype.card_fin] at this
        exact (pow_le_pow_left₀ (norm_nonneg _) h2 2).trans this
      have h4 : Real.exp (-2 * (s - 1) * t) = Real.exp (t) ^ 2 * Real.exp (-2 * s * t) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      have h5 : (0 : ℝ) < Real.exp (-2 * s * t) := Real.exp_pos _
      calc _ ≤ ((n : ℝ) * ∑ k, (C * Real.exp t * ‖h k t‖) ^ 2) * Real.exp (-2 * s * t) :=
            mul_le_mul_of_nonneg_right h3 h5.le
        _ = _ := by
          rw [h4, mul_sum, mul_sum, sum_mul]
          refine sum_congr rfl fun k _ => ?_
          ring
    have e1 : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have e2 : ∑ k, G k t = ENNReal.ofReal (∑ k, ‖h k t‖ ^ 2 * Real.exp (-2 * (s - 1) * t)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
      refine sum_congr rfl fun k _ => ?_
      rw [hG]
      simp only
      rw [e1, ENNReal.ofReal_mul (by positivity)]
    rw [e1, e2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  calc _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((n : ℝ) * C ^ 2) * ∑ k, G k t :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal ((n : ℝ) * C ^ 2) * ∑ k, ∫⁻ t in Set.Ioi (0 : ℝ), G k t := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ fun k _ => hmeas k]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.mpr fun k _ => hfin k)

section Family

variable {X : GMod n} {ι : Type} {c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}

theorem line_hasDeriv (hc : IsCoefFam ε X c) (i : ι) (u : X.V) {Y g : Matrix (Fin n) (Fin n) ℂ}
    (hY : Formalism.REAL.inG ε Y) (hg : Formalism.REAL.inUJ ε g) (s : ℝ) :
    HasDerivAt (fun t : ℝ => c i u (g * NormedSpace.exp ((t : ℂ) • Y)))
      (c i (actM X.E Y u) (g * NormedSpace.exp ((s : ℂ) • Y))) s := by
  have hgs : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((s : ℂ) • Y)) :=
    mul_inUJ hg (Formalism.REAL.exp_indefinite_unitary_holds n ε Y hY s)
  have h0 := hc.1 i u Y hY _ hgs
  have h0' : HasDerivAt (fun t : ℝ => c i u (g * NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)))
      (c i (actM X.E Y u) (g * NormedSpace.exp ((s : ℂ) • Y))) (s - s) := by
    rw [sub_self]
    exact h0
  have h1 : HasDerivAt (fun t : ℝ => c i u (g * NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp (((t - s : ℝ) : ℂ) • Y)))
      (c i (actM X.E Y u) (g * NormedSpace.exp ((s : ℂ) • Y))) s :=
    HasDerivAt.comp_sub_const s s h0'
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show c i u (g * NormedSpace.exp ((t : ℂ) • Y)) =
    c i u (g * NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp (((t - s : ℝ) : ℂ) • Y))
  rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _), ← add_smul]
  push_cast
  ring_nf

theorem line_cont (hc : IsCoefFam ε X c) (i : ι) (u : X.V) {Y g : Matrix (Fin n) (Fin n) ℂ}
    (hY : Formalism.REAL.inG ε Y) (hg : Formalism.REAL.inUJ ε g) :
    Continuous (fun t : ℝ => c i u (g * NormedSpace.exp ((t : ℂ) • Y))) :=
  continuous_iff_continuousAt.2 fun s => (line_hasDeriv hc i u hY hg s).continuousAt

def incl (X : GMod n) (z : ℂ) : (step X z).V →ₗ[ℂ] (Fin n → X.V) := (stepSub X z).subtype

theorem stepCoef_apply (X : GMod n) (z : ℂ) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n)
    (u : (step X z).V) (g : Matrix (Fin n) (Fin n) ℂ) :
    stepCoef X z c j u g = ∑ k, g j k * c (incl X z u k) g := rfl

theorem incl_E (X : GMod n) (z : ℂ) (a b : Fin n) (u : (step X z).V) :
    incl X z ((step X z).E a b u) = tensE X a b (incl X z u) := rfl

theorem incl_actM (X : GMod n) (z : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (u : (step X z).V) :
    incl X z (actM (step X z).E Y u) = actM (tensE X) Y (incl X z u) := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, incl_E]

theorem actM_tens_apply (X : GMod n) (Y : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → X.V) (k : Fin n) :
    actM (tensE X) Y v k = actM X.E Y (v k) + ∑ b, Y k b • v b := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, tensE_apply,
    smul_add, sum_add_distrib]
  congr 1
  simp [smul_ite, Finset.sum_ite_eq]

theorem step_right (hc : IsCoefFam ε X c) (z : ℂ) (i : ι) (j : Fin n) (u : (step X z).V)
    {Y g : Matrix (Fin n) (Fin n) ℂ} (hY : Formalism.REAL.inG ε Y) (hg : Formalism.REAL.inUJ ε g) :
    HasDerivAt (fun t : ℝ => stepCoef X z (c i) j u (g * NormedSpace.exp ((t : ℂ) • Y)))
      (stepCoef X z (c i) j (actM (step X z).E Y u) g) 0 := by
  have hg0 : ∀ k, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j k) ((g * Y) j k) 0 := by
    intro k
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun l _ => (CCRuleCW.entry_hasDerivAt Y l k).const_mul (g j l)
  have hc0 : ∀ k, HasDerivAt (fun t : ℝ => c i (incl X z u k) (g * NormedSpace.exp ((t : ℂ) • Y)))
      (c i (actM X.E Y (incl X z u k)) g) 0 := fun k => hc.1 i _ Y hY g hg
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Fin n))) fun k _ => (hg0 k).mul (hc0 k)
  refine hsum.congr_deriv ?_
  simp only [stepCoef_apply, incl_actM, actM_tens_apply, map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one, mul_add,
    sum_add_distrib]
  rw [add_comm]
  congr 1
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem finsupp_sum_comm (L : ι →₀ ℂ) (w : Fin n → ℂ) (φ : ι → Fin n → ℂ) :
    (L.sum fun i r => r * ∑ k, w k * φ i k) = ∑ k, w k * L.sum fun i r => r * φ i k := by
  unfold Finsupp.sum
  simp only [Finset.mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem step_left (hc : IsCoefFam ε X c) (z : ℂ) (i : ι) (j : Fin n) :
    ∃ l : Fin n → Fin n → (ι × Fin n) →₀ ℂ, ∀ (a b : Fin n) (u : (step X z).V) (g : Matrix (Fin n) (Fin n) ℂ),
      Formalism.REAL.inUJ ε g →
      stepCoef X z (c i) j ((step X z).E a b u) g = ∑ c', ∑ d,
        (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c' d *
          (l c' d).sum fun q r => r * stepCoef X z (c q.1) q.2 u g := by
  classical
  obtain ⟨l, hl⟩ := hc.2 i
  refine ⟨fun c' d => (l c' d).mapDomain (fun i' => (i', j)) + if c' = j then Finsupp.single (i, d) 1 else 0,
    fun a b u g hg => ?_⟩
  set M : Matrix (Fin n) (Fin n) ℂ := g * Matrix.single a b (1 : ℂ) * g⁻¹ with hM
  have key : ∀ c' d, ((l c' d).mapDomain (fun i' => (i', j)) + if c' = j then Finsupp.single (i, d) 1 else 0).sum
      (fun q r => r * stepCoef X z (c q.1) q.2 u g) =
      (l c' d).sum (fun i' r => r * stepCoef X z (c i') j u g) +
        if c' = j then stepCoef X z (c i) d u g else 0 := by
    intro c' d
    rw [Finsupp.sum_add_index' (fun q => zero_mul _) (fun q r s => add_mul _ _ _),
      Finsupp.sum_mapDomain_index (fun q => zero_mul _) (fun q r s => add_mul _ _ _)]
    congr 1
    split_ifs
    · simp
    · simp
  simp only [key, mul_add, sum_add_distrib]
  have hMg : ∀ k, ∑ d, M j d * g d k = if k = b then g j a else 0 := by
    intro k
    have e : M * g = g * Matrix.single a b (1 : ℂ) := by
      rw [hM, Matrix.mul_assoc, inv_mul_of_inUJ hg, Matrix.mul_one]
    have e2 := congrFun (congrFun e j) k
    rw [Matrix.mul_apply] at e2
    rw [e2]
    simp only [Matrix.mul_apply, Matrix.single_apply]
    by_cases hk : k = b
    · subst hk
      simp
    · have hk' : ¬ b = k := fun h => hk h.symm
      simp [hk, hk']
  have hS : ∀ c' d, (l c' d).sum (fun i' r => r * stepCoef X z (c i') j u g) =
      ∑ k, g j k * (l c' d).sum fun i' r => r * c i' (incl X z u k) g := fun c' d =>
    finsupp_sum_comm (l c' d) (fun k => g j k) (fun i' k => c i' (incl X z u k) g)
  have h1 : ∑ k, g j k * c i (X.E a b (incl X z u k)) g = ∑ c', ∑ d, M c' d *
      (l c' d).sum (fun i' r => r * stepCoef X z (c i') j u g) := by
    simp only [hS, hl a b _ g hg, ← hM, Finset.mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun c' _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun d _ => sum_congr rfl fun k _ => by ring
  have h2 : ∑ c', ∑ d, M c' d * (if c' = j then stepCoef X z (c i) d u g else 0) =
      g j a * c i (incl X z u b) g := by
    have e : ∀ c', ∑ d, M c' d * (if c' = j then stepCoef X z (c i) d u g else 0) =
        if c' = j then ∑ d, M j d * stepCoef X z (c i) d u g else 0 := by
      intro c'
      split_ifs with h
      · rw [h]
      · simp
    rw [sum_congr rfl fun c' _ => e c', Finset.sum_ite_eq' univ j, if_pos (mem_univ j)]
    calc ∑ d, M j d * stepCoef X z (c i) d u g
        = ∑ k, (∑ d, M j d * g d k) * c i (incl X z u k) g := by
          simp only [stepCoef_apply, Finset.mul_sum, Finset.sum_mul]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ = ∑ k, (if k = b then g j a else 0) * c i (incl X z u k) g :=
          sum_congr rfl fun k _ => by rw [hMg k]
      _ = g j a * c i (incl X z u b) g := by simp
  rw [← h1, h2]
  simp only [stepCoef_apply, incl_E, tensE_apply, map_add, Pi.add_apply, mul_add, sum_add_distrib]
  congr 1
  have e : ∀ x, g j x * c i (if x = a then incl X z u b else 0) g =
      if x = a then g j a * c i (incl X z u b) g else 0 := by
    intro x
    split_ifs with h
    · rw [h]
    · simp
  simp only [e]
  simp

end Family

theorem inv_combine (W g : Matrix (Fin n) (Fin n) ℂ) (hW : W * g = 1) (φ : Fin n → ℂ) (k : Fin n) :
    φ k = ∑ j, W k j * ∑ l, g j l * φ l := by
  calc φ k = ∑ l, (W * g) k l * φ l := by
        rw [hW]
        simp [Matrix.one_apply]
    _ = _ := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem stepFam : StepFam := by
  intro n ε X ι c z A μ hc hA
  have hfam : IsCoefFam ε (step X z) (fun p : ι × Fin n => stepCoef X z (c p.1) p.2) :=
    ⟨fun p u Y hY g hg => step_right hc z p.1 p.2 u hY hg, fun p => step_left hc z p.1 p.2⟩
  obtain ⟨C, hC0, hC⟩ := exp_entry_bound hA.2.2.1
  refine ⟨hfam, fun s u => ⟨fun h p => ?_, fun h k i => ?_⟩⟩
  · filter_upwards [ae_all_iff.2 fun k => h k p.1] with x hx
    have hx' : Formalism.REAL.inUJ ε (S7.toM x) := x.2
    refine lint_lt_top (s := s) (C := (∑ a, ∑ b, ‖S7.toM x a b‖) * C)
      (f := fun t => stepCoef X z (c p.1) p.2 u (S7.toM x * NormedSpace.exp ((t : ℂ) • A)))
      (h := fun k t => c p.1 (incl X z u k) (S7.toM x * NormedSpace.exp ((t : ℂ) • A)))
      (w := fun k t => (S7.toM x * NormedSpace.exp ((t : ℂ) • A)) p.2 k)
      (fun t _ => rfl) (fun k t ht => ?_) (fun k => line_cont hc _ _ hA.1 hx') (fun k => hx k)
    rw [mul_assoc]
    exact mul_entry_le _ _ (fun a b => (hC t ht.le a b).1) _ _
  · filter_upwards [ae_all_iff.2 fun j => h (i, j)] with x hx
    have hx' : Formalism.REAL.inUJ ε (S7.toM x) := x.2
    have hinv : ∀ t : ℝ, (NormedSpace.exp (-((t : ℂ) • A)) * (S7.toM x)⁻¹) *
        (S7.toM x * NormedSpace.exp ((t : ℂ) • A)) = 1 := by
      intro t
      have e1 : NormedSpace.exp (-((t : ℂ) • A)) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
        rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • A))), neg_add_cancel,
          NormedSpace.exp_zero]
      calc _ = NormedSpace.exp (-((t : ℂ) • A)) * ((S7.toM x)⁻¹ * S7.toM x) * NormedSpace.exp ((t : ℂ) • A) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [inv_mul_of_inUJ hx', Matrix.mul_one, e1]
    refine lint_lt_top (s := s + 1) (C := (∑ a, ∑ b, ‖((S7.toM x)⁻¹ : Matrix (Fin n) (Fin n) ℂ) a b‖) * C)
      (f := fun t => c i (incl X z u k) (S7.toM x * NormedSpace.exp ((t : ℂ) • A)))
      (h := fun j t => stepCoef X z (c i) j u (S7.toM x * NormedSpace.exp ((t : ℂ) • A)))
      (w := fun j t => (NormedSpace.exp (-((t : ℂ) • A)) * (S7.toM x)⁻¹) k j)
      (fun t _ => ?_) (fun j t ht => ?_) (fun j => line_cont hfam (i, j) u hA.1 hx') (fun j => ?_)
    · exact inv_combine _ _ (hinv t) (fun l => c i (incl X z u l) (S7.toM x * NormedSpace.exp ((t : ℂ) • A))) k
    · rw [mul_assoc]
      exact mul_entry_le' _ _ (fun a b => (hC t ht.le a b).2) _ _
    · rw [add_sub_cancel_right]
      exact hx j

end GlobalTheory.CompanionTheory.RgStepFam
