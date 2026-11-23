import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ConverseGL3

local notation "A" => algebraMap ℚ 𝔸[ℚ]

theorem vecCoeff_one_eq_zero {ι : Type*} [Fintype ι] {ξ : ι → ℚ} (h : ξ ≠ 0) :
    vecCoeff (fun _ : ι → 𝔸[ℚ] => (1 : ℂ)) ξ = 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : ξ i ≠ 0 := hi
  obtain ⟨t, ht⟩ : ∃ t, adelicChar ℚ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact adelicChar_ne_one (K := ℚ) (by ext t; simp [hc t])
  have hpa : pair ξ (Pi.single i (A (ξ i)⁻¹ * t)) = t := by
    rw [pair, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ i) hh
  have key := vecCoeff_translate (K := ℚ) (ι := ι) (f := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
    (Pi.single i (A (ξ i)⁻¹ * t)) ξ
  rw [hpa] at key
  have h1 : ((adelicChar ℚ t : Circle) : ℂ) ≠ 1 := fun e => ht (Circle.ext (by simpa using e))
  have h2 : (1 - ((adelicChar ℚ t : Circle) : ℂ)) * vecCoeff (fun _ : ι → 𝔸[ℚ] => (1 : ℂ)) ξ = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm h1))

theorem setIntegral_char_eq_zero {ι : Type*} [Fintype ι] {ξ : ι → ℚ} (h : ξ ≠ 0) :
    ∫ y in vecDomain ℚ ι, (adelicChar ℚ (pair ξ y) : ℂ) ∂vecMeasure ℚ ι = 0 := by
  have h' : -ξ ≠ 0 := neg_ne_zero.2 h
  have := vecCoeff_one_eq_zero h'
  simpa [vecCoeff, pair_neg_left] using this

local instance countable_GL2 : Countable (GL (Fin 2) ℚ) :=
  Function.Injective.countable (f := fun (γ : GL (Fin 2) ℚ) (i j : Fin 2) => γ.val i j)
    fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)

theorem setIntegral_tsum_eq_zero {ι : Type*} [Fintype ι] {F : NQ → (ι → 𝔸[ℚ]) → ℂ}
    (hc : ∀ q, Continuous (F q)) {b : NQ → ℝ} (hb : Summable b)
    (hbd : ∀ q y, y ∈ vecDomain ℚ ι → ‖F q y‖ ≤ b q)
    (h0 : ∀ q, ∫ y in vecDomain ℚ ι, F q y ∂vecMeasure ℚ ι = 0) :
    ∫ y in vecDomain ℚ ι, ∑' q, F q y ∂vecMeasure ℚ ι = 0 := by
  have hμ1 : ((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]
  haveI : IsFiniteMeasure ((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)) :=
    ⟨by rw [hμ1]; exact ENNReal.one_lt_top⟩
  have hae : ∀ q, ∀ᵐ y ∂((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)), ‖F q y‖ ≤ b q := fun q =>
    (ae_restrict_iff' measurableSet_vecDomain).2 (ae_of_all _ (hbd q))
  have hi : ∀ q, Integrable (F q) ((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)) := fun q =>
    Integrable.mono' (integrable_const (b q)) (hc q).aestronglyMeasurable (hae q)
  have hle : ∀ q, ∫ y, ‖F q y‖ ∂((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)) ≤ b q := fun q => by
    have := integral_mono_ae (hi q).norm (integrable_const (b q)) (hae q)
    simpa [measureReal_def, hμ1] using this
  have hs : Summable fun q => ∫ y, ‖F q y‖ ∂((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)) :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hle hb
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  simp [h0]

theorem diag_embed_mul_upper (γ : GL (Fin 2) ℚ) (u v : 𝔸[ℚ]) :
    dia (e1 γ) * uni 0 u v =
      uni 0 (A (γ.val 0 0) * u + A (γ.val 0 1) * v) (A (γ.val 1 0) * u + A (γ.val 1 1) * v) * dia (e1 γ) := by
  have D : ∀ a b, (dia (e1 γ)).val a b = A ((b1M γ.val) a b) := fun _ _ => rfl
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, D]
  fin_cases i <;> fin_cases j <;> simp [uni, b1M] <;> ring

theorem diag_embed_mul_lower (γ : GL (Fin 2) ℚ) (h11 : γ.val 1 1 = 0) {t : ℚ} (ht : t * γ.val 1 0 = γ.val 0 1)
    (c : 𝔸[ℚ]) : dia (e1 γ) * lowM c = uni (A t * c) 0 0 * dia (e1 γ) := by
  have D : ∀ a b, (dia (e1 γ)).val a b = A ((b1M γ.val) a b) := fun _ _ => rfl
  have ht' : A t * A (γ.val 1 0) = A (γ.val 0 1) := by rw [← map_mul, ht]
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, D]
  fin_cases i <;> fin_cases j <;> simp [uni, lowM, b1M, h11]
  linear_combination (-c) * ht'

theorem lowM_mul_uni (c z : 𝔸[ℚ]) : lowM c * uni 0 0 z = uni 0 0 z * lowM c := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [uni, lowM, mul_comm]

theorem continuous_uni {X : Type*} [TopologicalSpace X] {y z : X → 𝔸[ℚ]} (hy : Continuous y)
    (hz : Continuous z) : Continuous fun t => (uni 0 (y t) (z t) : G3) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => ?_,
    continuous_pi fun a => continuous_pi fun b => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [uni, Function.comp_def] <;> first | exact continuous_const | assumption
  · show Continuous fun t => (!![1, -0, 0 * z t - y t; 0, 1, -z t; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop

theorem continuous_lowM {X : Type*} [TopologicalSpace X] {c : X → 𝔸[ℚ]} (hc : Continuous c) :
    Continuous fun t => (lowM (c t) : G3) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => ?_,
    continuous_pi fun a => continuous_pi fun b => ?_⟩
  · show Continuous fun t => (!![1, 0, 0; c t, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop
  · show Continuous fun t => (!![1, 0, 0; -c t, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop

theorem det_ne_zero (γ : GL (Fin 2) ℚ) : γ.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

theorem term_Y {W : G3 → ℂ} (hpsi : ∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g)
    (γ : GL (Fin 2) ℚ) (g : G3) :
    ∫ y in vecDomain ℚ (Fin 2), W (dia (e1 γ) * (uni 0 (y 0) (y 1) * g)) ∂vecMeasure ℚ (Fin 2) = 0 := by
  have hne : ![γ.val 1 0, γ.val 1 1] ≠ 0 := by
    intro h
    have h0 : γ.val 1 0 = 0 := congrFun h 0
    have h1 : γ.val 1 1 = 0 := congrFun h 1
    exact det_ne_zero γ (by rw [Matrix.det_fin_two, h0, h1]; ring)
  have e : ∀ y : Fin 2 → 𝔸[ℚ], W (dia (e1 γ) * (uni 0 (y 0) (y 1) * g)) =
      (adelicChar ℚ (pair ![γ.val 1 0, γ.val 1 1] y) : ℂ) * W (dia (e1 γ) * g) := by
    intro y
    rw [← mul_assoc, diag_embed_mul_upper, mul_assoc, hpsi, zero_add]
    simp [pair, Fin.sum_univ_two]
  simp_rw [e]
  rw [integral_mul_const, setIntegral_char_eq_zero hne, zero_mul]

theorem W_lowM_uni {W : G3 → ℂ}
    (hpsi : ∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g)
    (γ : GL (Fin 2) ℚ) (c z : 𝔸[ℚ]) (g : G3) :
    W (dia (e1 γ) * (lowM c * uni 0 0 z * g)) =
      (adelicChar ℚ (A (γ.val 1 1) * z) : ℂ) * W (dia (e1 γ) * (lowM c * g)) := by
  rw [lowM_mul_uni, mul_assoc, ← mul_assoc (dia _), diag_embed_mul_upper, mul_assoc, hpsi]
  simp

theorem term_Y' {W : G3 → ℂ} (hc : Continuous W)
    (hpsi : ∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g)
    (γ : GL (Fin 2) ℚ) (g : G3) :
    ∫ y in vecDomain ℚ (Fin 2), W (dia (e1 γ) * (lowM (y 0) * uni 0 0 (y 1) * g))
      ∂vecMeasure ℚ (Fin 2) = 0 := by
  by_cases h11 : γ.val 1 1 = 0
  · have hd := det_ne_zero γ
    rw [Matrix.det_fin_two, h11, mul_zero, zero_sub] at hd
    have h10 : γ.val 1 0 ≠ 0 := fun h => hd (by rw [h, mul_zero, neg_zero])
    have h01 : γ.val 0 1 ≠ 0 := fun h => hd (by rw [h, zero_mul, neg_zero])
    have ht : (γ.val 0 1 / γ.val 1 0) * γ.val 1 0 = γ.val 0 1 := div_mul_cancel₀ _ h10
    have hne : ![γ.val 0 1 / γ.val 1 0, 0] ≠ 0 := fun h =>
      div_ne_zero h01 h10 (congrFun h 0)
    have e : ∀ y : Fin 2 → 𝔸[ℚ], W (dia (e1 γ) * (lowM (y 0) * uni 0 0 (y 1) * g)) =
        (adelicChar ℚ (pair ![γ.val 0 1 / γ.val 1 0, 0] y) : ℂ) * W (dia (e1 γ) * g) := by
      intro y
      rw [W_lowM_uni hpsi, h11, ← mul_assoc (dia _), diag_embed_mul_lower γ h11 ht, mul_assoc, hpsi]
      simp [pair, Fin.sum_univ_two]
    simp_rw [e]
    rw [integral_mul_const, setIntegral_char_eq_zero hne, zero_mul]
  · have hH : Continuous fun c : 𝔸[ℚ] => W (dia (e1 γ) * (lowM c * g)) :=
      hc.comp (continuous_const.mul ((continuous_lowM continuous_id).mul continuous_const))
    have hcont : Continuous fun y : Fin 2 → 𝔸[ℚ] =>
        (adelicChar ℚ (A (γ.val 1 1) * y 1) : ℂ) * W (dia (e1 γ) * (lowM (y 0) * g)) :=
      (continuous_subtype_val.comp (continuous_adelicChar.comp
        (continuous_const.mul (continuous_apply 1)))).mul (hH.comp (continuous_apply 0))
    simp_rw [W_lowM_uni hpsi]
    rw [setIntegral_vecDomain_sum (finSumFinEquiv (m := 1) (n := 1)).symm hcont]
    refine (setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_).trans (integral_zero _ _)
    have hne : ![γ.val 1 1] ≠ 0 := fun h => h11 (congrFun h 0)
    have hz := setIntegral_char_eq_zero hne
    have hp : ∀ y : Fin 1 → 𝔸[ℚ], pair ![γ.val 1 1] y = A (γ.val 1 1) * y 0 := fun y => by
      simp [pair]
    simp_rw [hp] at hz
    show ∫ y in vecDomain ℚ (Fin 1), (adelicChar ℚ (A (γ.val 1 1) * y 0) : ℂ) *
      W (dia (e1 γ) * (lowM (x 0) * g)) ∂vecMeasure ℚ (Fin 1) = 0
    rw [integral_mul_const, hz, zero_mul]

theorem CtU_of (h : MajU) (h2 : ContW) : CtU := by
  intro V hV W hW g
  have hc := h2 V hV W hW
  have hpsi := hV.psi W hW
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_vecDomain (K := ℚ) (ι := Fin 2)
  refine ⟨?_, ?_⟩
  · have hcont : Continuous fun y : Fin 2 → 𝔸[ℚ] => (uni 0 (y 0) (y 1) * g : G3) :=
      (continuous_uni (continuous_apply 0) (continuous_apply 1)).mul continuous_const
    obtain ⟨b, hb, hbd⟩ := h V hV W hW _ (hC.image hcont)
    exact setIntegral_tsum_eq_zero
      (F := fun q y => W (dia (e1 q.out) * (uni 0 (y 0) (y 1) * g)))
      (fun q => hc.comp (continuous_const.mul hcont)) hb
      (fun q y hy => hbd q _ ⟨y, hDC hy, rfl⟩) (fun q => term_Y hpsi q.out g)
  · have hcont : Continuous fun y : Fin 2 → 𝔸[ℚ] => (lowM (y 0) * uni 0 0 (y 1) * g : G3) :=
      ((continuous_lowM (continuous_apply 0)).mul
        (continuous_uni continuous_const (continuous_apply 1))).mul continuous_const
    obtain ⟨b, hb, hbd⟩ := h V hV W hW _ (hC.image hcont)
    exact setIntegral_tsum_eq_zero
      (F := fun q y => W (dia (e1 q.out) * (lowM (y 0) * uni 0 0 (y 1) * g)))
      (fun q => hc.comp (continuous_const.mul hcont)) hb
      (fun q y hy => hbd q _ ⟨y, hDC hy, rfl⟩) (fun q => term_Y' hc hpsi q.out g)

end GlobalTheory.CompanionTheory.ConverseGL3
