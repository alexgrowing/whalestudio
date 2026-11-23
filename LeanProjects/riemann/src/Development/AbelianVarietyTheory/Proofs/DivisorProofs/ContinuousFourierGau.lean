import Mathlib

noncomputable section

open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform

namespace GlobalTheory.RealWeil

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def gau (u : V) : ℂ := cexp (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2)

def IsHeis (om : V → V → ℝ) (ρ : V → B →L[ℂ] B) : Prop :=
  (∀ f, ρ 0 f = f) ∧ (∀ u v f, ρ u (ρ v f) = cexp (π * I * (om u v : ℂ)) • ρ (u + v) f) ∧
    (∀ u f, ‖ρ u f‖ = ‖f‖) ∧ ∀ f, Continuous fun u => ρ u f

def Sm (ρ : V → B →L[ℂ] B) (f : B) : Prop := ContDiff ℝ ∞ fun v => ρ v f

def IsOsc (ρ : V → B →L[ℂ] B) {G : Type} [Group G] (k : G → V → V) (Ω : G → B → B) : Prop :=
  (∀ g f f', Sm ρ f → Sm ρ f' → Ω g (f + f') = Ω g f + Ω g f') ∧
  (∀ g (a : ℂ) f, Sm ρ f → Ω g (a • f) = a • Ω g f) ∧
  (∀ g f, Sm ρ f → Sm ρ (Ω g f)) ∧
  (∀ f, Sm ρ f → Ω 1 f = f) ∧
  (∀ g g' f, Sm ρ f → Ω (g * g') f = Ω g (Ω g' f)) ∧
  (∀ g v f, Sm ρ f → Ω g (ρ v f) = ρ (k g v) (Ω g f)) ∧
  (∀ g (A : B →L[ℂ] B), (∀ v f, A (ρ v f) = ρ v (A f)) → ∀ f, Sm ρ f → Ω g (A f) = A (Ω g f)) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H),
    (∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) → ∀ g f, Sm ρ f → ‖Φ (Ω g f)‖ = ‖Φ f‖

theorem norm_gau (u : V) : ‖gau u‖ = Real.exp (-(π / 2) * ‖u‖ ^ 2) := by
  unfold gau
  rw [Complex.norm_exp]
  congr 1
  have : (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2) = ((-(π / 2) * ‖u‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_re]

theorem norm_gau_le_one (u : V) : ‖gau u‖ ≤ 1 := by
  rw [norm_gau, Real.exp_le_one_iff]
  have := Real.pi_pos
  nlinarith [sq_nonneg ‖u‖]

theorem gau_ne_zero (u : V) : gau u ≠ 0 := Complex.exp_ne_zero _

theorem gau_zero : gau (0 : V) = 1 := by simp [gau]

theorem gau_neg (u : V) : gau (-u) = gau u := by simp [gau]

theorem continuous_gau : Continuous (gau : V → ℂ) := by unfold gau; fun_prop

theorem IsHeis.twist {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) (g : V →L[ℝ] V)
    (hg : ∀ x y, om (g x) (g y) = om x y) : IsHeis om fun v => ρ (g v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hg, map_add], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp g.continuous⟩

theorem IsHeis.continuous {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) {Y : Type} [TopologicalSpace Y]
    {a : Y → V} {x : Y → B} (ha : Continuous a) (hx : Continuous x) : Continuous fun y => ρ (a y) (x y) := by
  have : Continuous fun p : B × V => ρ p.2 p.1 :=
    continuous_prod_of_continuous_lipschitzWith (fun p : B × V => ρ p.2 p.1) 1
      (fun f => h.2.2.2 f) fun v => LipschitzWith.of_dist_le_mul fun x y => by
        simp only [dist_eq_norm, ← map_sub, h.2.2.1]; simp
  exact this.comp (hx.prodMk ha)

end General

def dP {ι : Type} [Fintype ι] [DecidableEq ι] (s g : Matrix ι ι ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)).det

section Inner

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def omJ (J : V ≃ₗᵢ[ℝ] V) (x y : V) : ℝ := ⟪x, J y⟫

def lam (g : V → V) : ℂ := ∫ u, gau u * gau (g u)

def mu (J : V ≃ₗᵢ[ℝ] V) (g₁ g₂ : V → V) : ℂ :=
  ∫ u, ∫ v, gau u * gau v * (cexp (π * I * (omJ J (g₁ u) (g₂ v) : ℂ)) * gau (g₁ u + g₂ v))

theorem integrable_gau : Integrable (gau : V → ℂ) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (π / 2 : ℂ)) (by simpa using Real.pi_pos) 0 0
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [gau]

variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

omit [CompleteSpace B] in
theorem IsHeis.integrable (h : IsHeis om ρ) (f : B) : Integrable fun u => gau u • ρ u f := by
  refine Integrable.mono' ((integrable_gau (V := V)).norm.mul_const ‖f‖)
    (continuous_gau.smul (h.2.2.2 f)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul, h.2.2.1]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace B] in
theorem IsHeis.continuous_gau_smul (h : IsHeis om ρ) (f : B) : Continuous fun u => gau u • ρ u f :=
  continuous_gau.smul (h.2.2.2 f)

def proj (h : IsHeis om ρ) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u, gau u • ρ u f
      map_add' := fun f f' => by
        rw [← integral_add (h.integrable f) (h.integrable f')]
        simp only [map_add, smul_add]
      map_smul' := fun a f => by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm a] }
    (∫ u : V, ‖gau u‖) fun f => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [norm_smul, h.2.2.1]
      rw [integral_mul_const]

omit [CompleteSpace B] in
theorem proj_apply (h : IsHeis om ρ) (f : B) : proj h f = ∫ u, gau u • ρ u f := rfl

def Good (h : IsHeis om ρ) (f : B) : Prop := ∀ n : ℕ, Integrable fun w => ‖w‖ ^ n * ‖proj h (ρ (-w) f)‖

variable {J : V ≃ₗᵢ[ℝ] V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem omJ_skew (hJ : ∀ x, J (J x) = -x) (x y : V) : omJ J y x = -omJ J x y := by
  unfold omJ
  rw [← J.inner_map_map, hJ, inner_neg_right, real_inner_comm]

theorem proj_translate (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (w : V) :
    proj h (ρ (-w) f) = ρ (-w) (𝓕 (fun u => gau u • ρ u f) (J w)) := by
  rw [proj_apply, Real.fourier_eq', ← ContinuousLinearMap.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [map_smul, h.2.1, smul_smul]
    rw [add_comm (-w) u, omJ_skew hJ u (-w)]
    congr 1
    have e : omJ J u (-w) = -⟪u, J w⟫ := by simp [omJ]
    rw [e, mul_right_comm _ (gau u), ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  · have := (Real.fourierIntegral_convergent_iff (J w)).2 (h.integrable f)
    simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul, Complex.ofReal_neg] using this

theorem Good.fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) (n : ℕ) :
    Integrable fun w => ‖w‖ ^ n * ‖𝓕 (fun u => gau u • ρ u f) w‖ := by
  have := hf n
  simp only [proj_translate hJ, h.2.2.1] at this
  rw [← J.measurePreserving.integrable_comp_emb J.toHomeomorph.measurableEmbedding]
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp

theorem continuous_fourier_gau (h : IsHeis om ρ) (f : B) : Continuous (𝓕 fun u => gau u • ρ u f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (h.integrable f)

theorem Good.integrable_fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Integrable (𝓕 fun u => gau u • ρ u f) := by
  have := hf.fourier hJ 0
  simp only [pow_zero, one_mul] at this
  exact (integrable_norm_iff (continuous_fourier_gau h f).aestronglyMeasurable).1 this

theorem Good.inversion (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    ∫ w, ρ w (proj h (ρ (-w) f)) = f := by
  have e : ∀ w, ρ w (proj h (ρ (-w) f)) = 𝓕 (fun u => gau u • ρ u f) (J w) := by
    intro w
    have h0 : omJ J w (-w) = 0 := by
      have := omJ_skew hJ w w
      have e : omJ J w (-w) = -omJ J w w := by simp [omJ]
      linarith
    rw [proj_translate hJ, h.2.1, h0, add_neg_cancel, h.1]
    simp
  simp only [e]
  rw [J.measurePreserving.integral_comp J.toHomeomorph.measurableEmbedding]
  have := congrFun ((h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f)
    (hf.integrable_fourier hJ)) 0
  rw [Real.fourierInv_eq] at this
  simpa [gau_zero, h.1] using this

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem contDiff_gau_inv : ContDiff ℝ ∞ fun u : V => (gau u)⁻¹ := by
  have : (fun u : V => (gau u)⁻¹) = fun u => cexp ((π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    rw [gau, ← Complex.exp_neg]
    push_cast
    ring_nf
  rw [this]
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)))

theorem Good.sm (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) : Sm ρ f := by
  have h1 := (h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f) (hf.integrable_fourier hJ)
  have h2 : ContDiff ℝ ∞ (𝓕 (𝓕 fun u => gau u • ρ u f)) := Real.contDiff_fourier fun n _ => hf.fourier hJ n
  have h3 : ContDiff ℝ ∞ fun u => gau u • ρ u f := by
    rw [← h1]
    have : 𝓕⁻ (𝓕 fun u => gau u • ρ u f) = fun u => 𝓕 (𝓕 fun u => gau u • ρ u f) (-u) := by
      funext u; rw [Real.fourierInv_eq_fourier_neg]
    rw [this]
    exact h2.comp contDiff_neg
  have : ContDiff ℝ ∞ fun u => (gau u)⁻¹ • gau u • ρ u f := (contDiff_gau_inv (V := V)).smul h3
  simpa only [smul_smul, inv_mul_cancel₀ (gau_ne_zero _), one_smul, Sm] using this

end Inner

end GlobalTheory.RealWeil

end
