import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix MeasureTheory Set Complex
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

namespace GlobalTheory.ChernReg

section Flat

variable {d : ℕ}

def polMat (q : (Fin d → ℂ) → ℝ) : Matrix (Fin d) (Fin d) ℂ := fun k l =>
  (q (Pi.single k 1 + Pi.single l 1) - q (Pi.single k 1 - Pi.single l 1) +
    I * q (Pi.single k 1 + I • Pi.single l 1) - I * q (Pi.single k 1 - I • Pi.single l 1)) / 4

def christoffel (b : V d → Matrix (Fin d) (Fin d) ℂ) (z ξ : V d) : V d :=
  WithLp.toLp 2 ((ξ.ofLp ᵥ* Matrix.of fun k l => del (fun v => b v k l) z ξ) ᵥ* (b z)⁻¹)

def jet (b : V d → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : V d × V d → V d :=
  n.rec Prod.fst fun _ f q => del f q (q.2, -christoffel b q.1 q.2)

theorem polMat_form {b : Matrix (Fin d) (Fin d) ℂ} (hb : b.IsHermitian) :
    polMat (fun ξ => (∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l)).re) = b := by
  ext k l
  have e (c : ℂ) : ((∑ k', ∑ l', b k' l' * (Pi.single k 1 + c • Pi.single l 1 : Fin d → ℂ) k' *
      starRingEnd ℂ ((Pi.single k 1 + c • Pi.single l 1 : Fin d → ℂ) l')).re : ℂ) =
      b k k + starRingEnd ℂ c * b k l + c * b l k + c * starRingEnd ℂ c * b l l := by
    have h : ∑ k', ∑ l', b k' l' * (Pi.single k 1 + c • Pi.single l 1 : Fin d → ℂ) k' *
      starRingEnd ℂ ((Pi.single k 1 + c • Pi.single l 1 : Fin d → ℂ) l') =
      b k k + starRingEnd ℂ c * b k l + c * b l k + c * starRingEnd ℂ c * b l l := by
      simp [Pi.single_apply, mul_add, add_mul, Finset.sum_add_distrib, apply_ite (starRingEnd ℂ)]
      ring
    rw [h]
    refine Complex.conj_eq_iff_re.1 ?_
    have h' (i j) : starRingEnd ℂ (b i j) = b j i := hb.apply j i
    simp only [map_add, map_mul, h', Complex.conj_conj]
    ring
  have e₁ := e 1
  have e₂ := e (-1)
  have e₃ := e I
  have e₄ := e (-I)
  rw [one_smul] at e₁
  rw [neg_one_smul, ← sub_eq_add_neg] at e₂
  rw [neg_smul, ← sub_eq_add_neg] at e₄
  rw [polMat, e₁, e₂, e₃, e₄]
  simp only [map_one, map_neg, conj_I]
  linear_combination ((b l k - b k l) / 2) * I_mul_I

theorem chris_vecMul {b : V d → Matrix (Fin d) (Fin d) ℂ} {z : V d} (h : IsUnit (b z).det) (ξ : V d) :
    (christoffel b z ξ).ofLp ᵥ* b z = ξ.ofLp ᵥ* Matrix.of fun k l => del (fun v => b v k l) z ξ := by
  rw [christoffel, WithLp.ofLp_toLp, vecMul_vecMul, nonsing_inv_mul _ h, vecMul_one]

variable (b : V d → Matrix (Fin d) (Fin d) ℂ)

theorem jet_zero : jet b 0 = Prod.fst := rfl

theorem jet_succ (n : ℕ) (q : V d × V d) : jet b (n + 1) q = del (jet b n) q (q.2, -christoffel b q.1 q.2) := rfl

theorem jet_one : jet b 1 = Prod.snd := funext fun q => by
  rw [jet_succ, jet_zero, del_eq_fderiv differentiableAt_fst, fderiv_fst]
  rfl

theorem jet_two (q : V d × V d) : jet b 2 q = -christoffel b q.1 q.2 := by
  rw [jet_succ, jet_one, del_eq_fderiv differentiableAt_snd, fderiv_snd]
  rfl

theorem jet_const (b : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : jet (fun _ => b) (n + 2) = fun _ => 0 := by
  induction n with
  | zero => exact funext fun q => by simp [jet_two, christoffel, show (of fun _ _ => 0 : Matrix (Fin d) (Fin d) ℂ) = 0 from rfl]
  | succ n ih => exact funext fun q => by rw [jet_succ, ih, del_const]; rfl

def cutoff (t : ℝ) : ℝ := if t < 1 then ((1 - t) ^ 2)⁻¹ * Real.exp (t - 1)⁻¹ else 0

theorem cutoff_nonneg (t : ℝ) : 0 ≤ cutoff t := by
  unfold cutoff
  split_ifs <;> positivity

theorem cutoff_pos_iff {t : ℝ} : 0 < cutoff t ↔ t < 1 := by
  unfold cutoff
  split_ifs with h
  · exact iff_of_true (mul_pos (inv_pos.2 (pow_pos (sub_pos.2 h) 2)) (Real.exp_pos _)) h
  · exact iff_of_false (lt_irrefl _) h

def mean (q f : (Fin d → ℂ) → ℝ) : ℝ := (∫ ξ, f ξ * cutoff (q ξ)) / ∫ ξ, cutoff (q ξ)

theorem mean_comp (q f : (Fin d → ℂ) → ℝ) (T : (Fin d → ℂ) ≃ₗ[ℝ] (Fin d → ℂ)) :
    mean (q ∘ T) (f ∘ T) = mean q f := by
  have hT := T.isUnit_det'.ne_zero
  have e (g : (Fin d → ℂ) → ℝ) : ∫ ξ, g (T ξ) = |(LinearMap.det T.toLinearMap)⁻¹| * ∫ ξ, g ξ := by
    have h := integral_map_equiv (μ := volume) T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv g
    have h' := Measure.map_linearMap_addHaar_eq_smul_addHaar volume hT
    refine h.symm.trans ((congrArg (fun μ => ∫ ξ, g ξ ∂μ) h').trans ?_)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
  exact (congrArg₂ (· / ·) (e fun ξ => f ξ * cutoff (q ξ)) (e fun ξ => cutoff (q ξ))).trans
    (mul_div_mul_left _ _ (abs_pos.2 (inv_ne_zero hT)).ne')

theorem cutoff_le (t : ℝ) : cutoff t ≤ 2 := by
  unfold cutoff
  split_ifs with h
  · have h₁ := Real.pow_div_factorial_le_exp (1 - t)⁻¹ (inv_pos.2 (sub_pos.2 h)).le 2
    rw [← neg_sub 1 t, inv_neg, Real.exp_neg, ← inv_pow, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    norm_num [Nat.factorial] at h₁ ⊢
    linarith
  · exact zero_le_two

theorem measurable_cutoff : Measurable cutoff :=
  Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

section Mass

variable {q : (Fin d → ℂ) → ℝ} (hc : Continuous q) (hh : ∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ)
  (hp : ∀ ξ, ξ ≠ 0 → 0 < q ξ)
include hc hh hp

theorem isBounded_ball : Bornology.IsBounded {ξ | q ξ < 1} := by
  obtain ⟨m, hm, h⟩ : ∃ m > 0, ∀ ξ ∈ Metric.sphere (0 : Fin d → ℂ) 1, m ≤ q ξ :=
    (isCompact_sphere 0 1).exists_forall_le' hc.continuousOn fun ξ hξ => hp ξ (by rintro rfl; simp at hξ)
  refine (Metric.isBounded_closedBall (x := 0) (r := max 1 m⁻¹)).subset fun ξ hξ => ?_
  rw [mem_closedBall_zero_iff, le_max_iff, or_iff_not_imp_left, not_le]
  intro h1
  have h0 : 0 < ‖ξ‖ := one_pos.trans h1
  have h2 := h (‖ξ‖⁻¹ • ξ) (by simp [norm_smul, h0.ne'])
  have h3 : q ξ < 1 := hξ
  rw [hh, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)] at h2
  rw [le_inv_comm₀ h0 hm, ← one_div, le_div_iff₀ h0]
  nlinarith [mul_pos hm h0]

theorem integrable_cutoff : Integrable fun ξ => cutoff (q ξ) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := {ξ | q ξ < 1}) fun ξ hξ =>
    cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' hξ)).1 ?_
  refine Measure.integrableOn_of_bounded (M := 2) (isBounded_ball hc hh hp).measure_lt_top.ne
    (measurable_cutoff.comp hc.measurable).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_of_nonneg (cutoff_nonneg _)]
  exact cutoff_le _

theorem mass_pos : 0 < ∫ ξ, cutoff (q ξ) := by
  rw [integral_pos_iff_support_of_nonneg (fun _ => cutoff_nonneg _) (integrable_cutoff hc hh hp)]
  refine lt_of_lt_of_le ((isOpen_lt hc continuous_const (g := fun _ => 1)).measure_pos volume ⟨0, ?_⟩)
    (measure_mono fun ξ hξ => (cutoff_pos_iff.2 hξ).ne')
  have := hh 0 0
  simp only [smul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
  exact this.trans_lt one_pos

theorem mean_const (r : ℝ) : mean q (fun _ => r) = r := by
  rw [mean, integral_const_mul, mul_div_cancel_right₀ _ (mass_pos hc hh hp).ne']

end Mass

end Flat

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ}

abbrev ChartMap (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) : Type := AlgChart p σ d → CxPts p σ → (Fin d → ℂ) → CxPts p σ

def matIn (a : ChartForm p σ d) (c : AlgChart p σ d) (v : V d) : Matrix (Fin d) (Fin d) ℂ := polMat (a c (c.e.symm v))

structure IsExph (a : ChartForm p σ d) (E : ChartMap p σ d) : Prop where

  trans : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E c y ξ = E c' y (c.dtrans c' y ξ)

  cont : ∀ c : AlgChart p σ d, ContinuousOn (fun q : V d × V d => E c (c.e.symm q.1) q.2.ofLp) (c.e.target ×ˢ univ)

  smooth : ∀ c c' : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × V d => c'.e (E c (c.e.symm q.1) q.2.ofLp))
    {q | q.1 ∈ c.e.target ∧ E c (c.e.symm q.1) q.2.ofLp ∈ c'.e.source}

  zero : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, E c y 0 = y

  jets : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ (ξ : V d) (n : ℕ),
    iteratedDeriv n (fun t : ℝ => c.e (E c y (t • ξ.ofLp))) 0 = jet (matIn a c) n (c.e y, ξ)

def ConjComm (j : CxPts p σ' → CxPts p σ) (E : ChartMap p σ d) (E' : ChartMap p σ' d) : Prop :=
  ∀ (c : AlgChart p σ d) (c' : AlgChart p σ' d),
    (∀ w ∈ c'.e.source, j w ∈ c.e.source → ∀ i, c'.e w i = starRingEnd ℂ (c.e (j w) i)) →
    ∀ z ∈ c'.e.source, j z ∈ c.e.source → ∀ ξ, j (E' c' z ξ) = E c (j z) (star ξ)

def rhoIn (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (c : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) : ℝ :=
  mean (a c y) fun ξ => ψ (E c y (t • ξ))

structure IsRegConst (a θ : ChartForm p σ d) (Ψ : CxPts p σ → ℝ → ℝ) (A K δ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  K_nonneg : 0 ≤ K
  δ_pos : 0 < δ
  smooth : ∀ c : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖)
    (c.e.target ×ˢ {w | 0 < ‖w‖ ∧ ‖w‖ < δ})
  mono : ∀ y, MonotoneOn (fun t => Ψ y t + K * t ^ 2) (Ioo 0 δ)
  hess : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → ∀ (ξ : V d) (η : ℂ),
    -(A * (‖w‖ * deriv (fun t => Ψ y t + K * t ^ 2) ‖w‖) * a c y ξ.ofLp) -
        K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) ≤
      θ c y ξ.ofLp + (leviForm (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y, w) (ξ, η) (ξ, η)).re / Real.pi

theorem isRegConst_const {a θ : ChartForm p σ d} (ha : ∀ c y ξ, 0 ≤ a c y ξ) (hθ : ∀ c y ξ, 0 ≤ θ c y ξ) (r : ℝ) {A K δ : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hδ : 0 < δ) : IsRegConst a θ (fun _ _ => r) A K δ where
  A_nonneg := hA
  K_nonneg := hK
  δ_pos := hδ
  smooth _ := contDiffOn_const
  mono _ s hs t _ h := by
    have := hs.1
    beta_reduce
    gcongr
  hess c y _ w _ _ ξ η := by
    have e : deriv (fun t : ℝ => r + K * t ^ 2) ‖w‖ = K * (2 * ‖w‖) := by
      simpa using (((hasDerivAt_pow 2 ‖w‖).const_mul K).const_add r).deriv
    have e' : dbar (fun _ : V d × ℂ => (r : ℂ)) = fun _ => 0 := funext fun _ => dbar_const _ _
    have := ha c y ξ.ofLp
    rw [e, leviForm, ddbar, e', del_const]
    have h₁ : 0 ≤ A * (‖w‖ * (K * (2 * ‖w‖))) * a c y ξ.ofLp := by positivity
    have h₂ : 0 ≤ K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) := by positivity
    have h₃ := hθ c y ξ.ofLp
    simp only [ContinuousLinearMap.zero_apply, zero_re, zero_div]
    linarith

variable {a : ChartForm p σ d} {E : ChartMap p σ d} {R : AnRead p σ d}

theorem rhoIn_eq (ha : IsKaehlerForm R a) (hE : IsExph a E) (ψ : CxPts p σ → ℝ) {c c' : AlgChart p σ d} {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) (t : ℝ) : rhoIn a E ψ c y t = rhoIn a E ψ c' y t := by
  let L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := (WithLp.linearEquiv 2 ℂ _).toLinearMap ∘ₗ
    (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y)).toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap
  have hL : Function.Injective (L.restrictScalars ℝ) := (injective_iff_map_eq_zero _).2 fun ξ h =>
    by_contra fun h0 => AlgChart.dtrans_ne_zero hy hy' h0 h
  let T := LinearEquiv.ofInjectiveEndo _ hL
  rw [rhoIn, rhoIn, ← mean_comp (a c' y) _ T]
  congr 1
  · exact funext fun ξ => ha.trans hy hy' ξ
  · exact funext fun ξ => congrArg ψ ((hE.trans c c' y hy hy' _).trans (congrArg _ (map_smul T t ξ)))

variable [SmoothOfRelativeDimension d p]

def rho (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (y : CxPts p σ) (t : ℝ) : ℝ :=
  rhoIn a E ψ (AlgChart.exists_mem_source (D := d) y).choose y t

theorem rho_eq (ha : IsKaehlerForm R a) (hE : IsExph a E) (ψ : CxPts p σ → ℝ) {c : AlgChart p σ d} {y : CxPts p σ}
    (hy : y ∈ c.e.source) (t : ℝ) : rho a E ψ y t = rhoIn a E ψ c y t :=
  rhoIn_eq ha hE ψ (AlgChart.exists_mem_source y).choose_spec hy t

omit [SmoothOfRelativeDimension d p] in

theorem exists_eq_sum (ha : IsKaehlerForm R a) {c : AlgChart p σ d} {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ b : Matrix (Fin d) (Fin d) ℂ, a c y = fun ξ => (∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l)).re / Real.pi :=
  have ⟨_, _, hW, _, _, e⟩ := ha.1 y
  ⟨_, funext fun ξ => e c y hy hW ξ⟩

omit [SmoothOfRelativeDimension d p] in

theorem continuous_and_smul (ha : IsKaehlerForm R a) {c : AlgChart p σ d} {y : CxPts p σ} (hy : y ∈ c.e.source) :
    Continuous (a c y) ∧ ∀ (t : ℝ) ξ, a c y (t • ξ) = t ^ 2 * a c y ξ := by
  obtain ⟨b, e⟩ := exists_eq_sum ha hy
  rw [e]
  refine ⟨by fun_prop, fun t ξ => ?_⟩
  rw [← mul_div_assoc, ← re_ofReal_mul]
  simp only [Finset.mul_sum, Pi.smul_apply, real_smul, map_mul, conj_ofReal, ofReal_pow]
  congr 2
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem rho_const (ha : IsKaehlerForm R a) (E : ChartMap p σ d) (r : ℝ) (y : CxPts p σ) (t : ℝ) :
    rho a E (fun _ => r) y t = r :=
  have hy := (AlgChart.exists_mem_source (D := d) y).choose_spec
  mean_const (continuous_and_smul ha hy).1 (continuous_and_smul ha hy).2 (ha.2 _ y hy) r

theorem rho_zero (ha : IsKaehlerForm R a) (hE : IsExph a E) (ψ : CxPts p σ → ℝ) (y : CxPts p σ) :
    rho a E ψ y 0 = ψ y := by
  have hy := (AlgChart.exists_mem_source (D := d) y).choose_spec
  rw [← rho_const ha E (ψ y) y 0]
  simp only [rho, rhoIn, zero_smul, hE.zero _ y hy]

end Manifold

end GlobalTheory.ChernReg
