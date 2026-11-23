import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGramChiDerivative
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HasDerivAtDet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology Metric ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M IntegralOfBergman
open scoped ComplexConjugate InnerProductSpace Matrix ComplexOrder

noncomputable section

namespace GramChiDerivative

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

lemma ptInner_sum {ι : Type*} [Fintype ι] (W : Weight L) (n : ℕ) (α β : ι → ℂ)
    (s : ι → Fin A.n → X → ℂ) (x : X) :
    ptInner W n (∑ c, α c • s c) (∑ d, β d • s d) x =
      ∑ c, ∑ d, α c * conj (β d) * ptInner W n (s c) (s d) x := by
  simp only [ptInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  ring

lemma ptInner_lerp (W₀ W₁ : Weight L) (n : ℕ) (f g : Fin A.n → X → ℂ) (s : ℝ) (x : X) :
    ptInner (W₀.lerp W₁ s) n f g x =
      ptInner W₀ n f g x * ((Real.exp (-(n : ℝ) * s * Weight.diff W₁ W₀ x) : ℝ) : ℂ) := by
  have h : ∀ a b : ℝ, Real.exp (-(n : ℝ) * (a + s * b)) =
      Real.exp (-(n : ℝ) * a) * Real.exp (-(n : ℝ) * s * b) := fun a b ↦ by
    rw [← Real.exp_add]; ring_nf
  simp only [ptInner, Weight.lerp, Weight.diff, h]
  push_cast
  ring

lemma hasDerivAt_integral_exp [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {F : X → ℂ} {u : X → ℝ} (hF : Continuous F)
    (hu : Continuous u) (c t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, F x * ((Real.exp (c * s * u x) : ℝ) : ℂ) ∂μ)
      (∫ x, F x * ((c * u x * Real.exp (c * t * u x) : ℝ) : ℂ) ∂μ) t := by
  obtain ⟨MF, hMF⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨MU, hMU⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
  have hcont : ∀ s, Continuous fun x ↦ F x * ((Real.exp (c * s * u x) : ℝ) : ℂ) := fun s ↦
    hF.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hu)))
  have hcont' : Continuous fun x ↦ F x * ((c * u x * Real.exp (c * t * u x) : ℝ) : ℂ) :=
    hF.mul (Complex.continuous_ofReal.comp ((continuous_const.mul hu).mul
      (Real.continuous_exp.comp (continuous_const.mul hu))))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x ↦ F x * ((Real.exp (c * s * u x) : ℝ) : ℂ))
    (F' := fun s x ↦ F x * ((c * u x * Real.exp (c * s * u x) : ℝ) : ℂ))
    (bound := fun _ ↦ MF * (|c| * MU * Real.exp (|c| * (|t| + 1) * MU)))
    (ball_mem_nhds t zero_lt_one) (Eventually.of_forall fun s ↦ (hcont s).aestronglyMeasurable)
    ((hcont t).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)
    hcont'.aestronglyMeasurable ?_ (integrable_const _) ?_).2
  · refine ae_of_all _ fun a s hs ↦ ?_
    have hF0 : ‖F a‖ ≤ MF := hMF a (mem_univ a)
    have hU0 : |u a| ≤ MU := by simpa [Real.norm_eq_abs] using hMU a (mem_univ a)
    have hMF0 : 0 ≤ MF := (norm_nonneg _).trans hF0
    have hMU0 : 0 ≤ MU := (abs_nonneg _).trans hU0
    have hs' : |s| ≤ |t| + 1 := by
      have h1 := mem_ball.1 hs
      rw [Real.dist_eq] at h1
      have h2 := abs_sub_abs_le_abs_sub s t
      linarith
    have hexp : c * s * u a ≤ |c| * (|t| + 1) * MU := by
      calc c * s * u a ≤ |c * s * u a| := le_abs_self _
        _ = |c| * |s| * |u a| := by rw [abs_mul, abs_mul]
        _ ≤ |c| * (|t| + 1) * MU :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs' (abs_nonneg c)) hU0 (abs_nonneg _)
            (mul_nonneg (abs_nonneg c) (by positivity))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    exact mul_le_mul hF0 (mul_le_mul (mul_le_mul_of_nonneg_left hU0 (abs_nonneg c))
      (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le (mul_nonneg (abs_nonneg c) hMU0))
      (by positivity) hMF0
  · refine ae_of_all _ fun a s _ ↦ ?_
    have h1 : HasDerivAt (fun r ↦ c * r * u a) (c * u a) s := by
      simpa using ((hasDerivAt_id s).const_mul c).mul_const (u a)
    have h3 := h1.exp.ofReal_comp
    refine (h3.const_mul (F a)).congr_deriv ?_
    push_cast
    ring

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma integral_ptInner_sum (W : Weight L) (dV : SmoothVolume A) {n : ℕ} {ι : Type*} [Fintype ι]
    (f : X → ℂ) (hf : Continuous f) (α β : ι → ℂ) (s : ι → Fin A.n → X → ℂ)
    (hs : ∀ c, s c ∈ L.sections n) :
    ∫ x, f x * ptInner W n (∑ c, α c • s c) (∑ d, β d • s d) x ∂dV.μ =
      ∑ c, ∑ d, α c * conj (β d) * ∫ x, f x * ptInner W n (s c) (s d) x ∂dV.μ := by
  have := dV.isProb
  have hint : ∀ c d, Integrable
      (fun x ↦ f x * (α c * conj (β d) * ptInner W n (s c) (s d) x)) dV.μ :=
    fun c d ↦ (hf.mul (continuous_const.mul (continuous_ptInner W (hs c) (hs d)))).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  simp_rw [ptInner_sum, Finset.mul_sum]
  rw [integral_finsetSum _ fun c _ ↦ integrable_finsetSum _ fun d _ ↦ hint c d]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [integral_finsetSum _ fun d _ ↦ hint c d]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

lemma gram_posDef (W : Weight L) (dV : SmoothVolume A) {n : ℕ}
    {V : Submodule ℂ (Fin A.n → X → ℂ)} (hV : V ≤ L.sections n) {m : ℕ}
    (e : Module.Basis (Fin m) ℂ V) :
    (gram W dV n (fun a ↦ (e a : Fin A.n → X → ℂ))).PosDef := by
  have := dV.isProb
  have hs : ∀ a, (e a : Fin A.n → X → ℂ) ∈ L.sections n := fun a ↦ hV (e a).2
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun y hy ↦ ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, gram, Matrix.of_apply, Complex.star_def]
    rw [← integral_conj]
    congr 1
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · set v : V := ∑ a, conj (y a) • e a with hv
    have hv0 : v ≠ 0 := by
      intro h0
      have h := (Fintype.linearIndependent_iff.1 e.linearIndependent) (fun a ↦ conj (y a)) h0
      exact hy (funext fun a ↦ by simpa using h a)
    have hvs : (v : Fin A.n → X → ℂ) = ∑ a, conj (y a) • (e a : Fin A.n → X → ℂ) := by
      simp [hv]
    have hpos := sectionL2NormSq_pos W dV (hV v.2) (by simpa using hv0)
    have key : star y ⬝ᵥ (gram W dV n (fun a ↦ (e a : Fin A.n → X → ℂ)) *ᵥ y) =
        ((sectionL2NormSq W dV n v : ℝ) : ℂ) := by
      rw [← integral_ptInner_self, hvs]
      have h := integral_ptInner_sum W dV (fun _ ↦ 1) continuous_const (fun a ↦ conj (y a))
        (fun a ↦ conj (y a)) _ hs
      simp only [one_mul, Complex.conj_conj] at h
      rw [h]
      simp only [dotProduct, Matrix.mulVec, gram, Matrix.of_apply, Pi.star_apply,
        Complex.star_def, Finset.mul_sum, ptInner]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
      ring
    rw [key]
    exact Complex.zero_lt_real.2 hpos

lemma trace_eq (W : Weight L) (dV : SmoothVolume A) {n : ℕ} {V : Submodule ℂ (Fin A.n → X → ℂ)}
    [FiniteDimensional ℂ V] (hV : V ≤ L.sections n)
    (e : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (f : X → ℂ) (hf : Continuous f) :
    ((gram W dV n (fun a ↦ (e a : Fin A.n → X → ℂ)))⁻¹ *
        Matrix.of (fun a a' ↦ ∫ x, f x * ptInner W n (e a : Fin A.n → X → ℂ) (e a') x ∂dV.μ)).trace =
      ∫ x, f x * (bergman W dV V n x : ℂ) ∂dV.μ := by
  have := dV.isProb
  have hdetG : IsUnit (gram W dV n (fun a ↦ (e a : Fin A.n → X → ℂ))).det :=
    (gram_posDef W dV hV e).det_pos.ne'.isUnit
  let ev : X → V →ₗ[ℂ] ℂ := fun x ↦
    { toFun := fun s ↦ (s : Fin A.n → X → ℂ) (chartIdx A x) x
      map_add' := fun s t ↦ by simp
      map_smul' := fun r s ↦ by simp }
  let c : InnerProductSpace.Core ℂ V := l2InnerCore W dV n V hV
  let _ : NormedAddCommGroup V := c.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  let b := stdOrthonormalBasis ℂ V
  have hnorm : ∀ s : V, ‖s‖ ^ 2 = sectionL2NormSq W dV n s := fun s ↦ by
    rw [@norm_sq_eq_re_inner ℂ]
    change (∫ x, ptInner W n (s : Fin A.n → X → ℂ) s x ∂dV.μ).re = _
    rw [integral_ptInner_self, Complex.ofReal_re]
  have hpt : ∀ (s : V) (x : X), ptNormSq W n (s : Fin A.n → X → ℂ) x =
      ‖ev x s‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) := fun s x ↦ rfl
  have hB : ∀ x, bergman W dV V n x = ∑ a, ptNormSq W n (b a : Fin A.n → X → ℂ) x := by
    intro x
    rw [bergman]
    simp_rw [hpt, ← hnorm]
    rw [iSup_ratio_eq b (ev x) _ (Real.exp_pos _).le, Finset.sum_mul]
  have hsb : ∀ c, (b c : Fin A.n → X → ℂ) ∈ L.sections n := fun c ↦ hV (b c).2
  let P : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    Matrix.of fun a c ↦ ⟪b c, e a⟫_ℂ
  have hcoe : ∀ a, (e a : Fin A.n → X → ℂ) = ∑ c, P a c • (b c : Fin A.n → X → ℂ) := by
    intro a
    conv_lhs => rw [← b.sum_repr' (e a)]
    rw [Submodule.coe_sum]
    rfl
  have hmat : ∀ g : X → ℂ, Continuous g →
      Matrix.of (fun a a' ↦ ∫ x, g x * ptInner W n (e a : Fin A.n → X → ℂ) (e a') x ∂dV.μ) =
        P * Matrix.of (fun c d ↦ ∫ x, g x * ptInner W n (b c : Fin A.n → X → ℂ) (b d) x ∂dV.μ) *
          Pᴴ := by
    intro g hg
    ext a a'
    rw [Matrix.of_apply, hcoe a, hcoe a', integral_ptInner_sum W dV g hg _ _ _ hsb]
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
    ring
  have hgram : gram W dV n (fun a ↦ (e a : Fin A.n → X → ℂ)) = P * Pᴴ := by
    have h1 := hmat (fun _ ↦ 1) continuous_const
    have h2 : Matrix.of (fun c d ↦ ∫ x, (fun _ ↦ (1 : ℂ)) x *
        ptInner W n (b c : Fin A.n → X → ℂ) (b d) x ∂dV.μ) = 1 := by
      ext c d
      rw [Matrix.of_apply, Matrix.one_apply]
      simp only [one_mul]
      change ⟪b d, b c⟫_ℂ = _
      rw [orthonormal_iff_ite.1 b.orthonormal d c]
      exact if_congr eq_comm rfl rfl
    rw [h2, Matrix.mul_one] at h1
    rw [← h1]
    ext a a'
    simp [gram, ptInner]
  have hP : IsUnit P.det := by
    rw [hgram, Matrix.det_mul] at hdetG
    exact isUnit_of_mul_isUnit_left hdetG
  have hPh : IsUnit Pᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hP.star
  have hfun : ∀ x, f x * (bergman W dV V n x : ℂ) =
      ∑ c, f x * ptInner W n (b c : Fin A.n → X → ℂ) (b c) x := by
    intro x
    rw [hB x, ← Finset.mul_sum]
    congr 1
    push_cast
    exact Finset.sum_congr rfl fun c _ ↦ (ptInner_self W n _ x).symm
  rw [hmat f hf, hgram, Matrix.mul_inv_rev]
  set M := Matrix.of (fun c d ↦ ∫ x, f x * ptInner W n (b c : Fin A.n → X → ℂ) (b d) x ∂dV.μ)
    with hM
  have e1 : Pᴴ⁻¹ * P⁻¹ * (P * M * Pᴴ) = (Pᴴ⁻¹ * (P⁻¹ * P) * M) * Pᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e1, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hPh, Matrix.one_mul]
  have hint : ∀ c, Integrable (fun x ↦ f x * ptInner W n (b c : Fin A.n → X → ℂ) (b c) x) dV.μ :=
    fun c ↦ (hf.mul (continuous_ptInner W (hsb c) (hsb c))).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  simp_rw [hfun]
  rw [integral_finsetSum _ fun c _ ↦ hint c, hM]
  rfl

end GramChiDerivative

open GramChiDerivative in

theorem GramChiDerivative.proof : GramChiDerivative.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV n V _ hV e t
  have := dV.isProb
  set u := Weight.diff W₁ W₀ with hu_def
  have hu : Continuous u := MetricChange.diff_continuous W₁ W₀
  have hE : ∀ a, (e a : Fin A.n → X → ℂ) ∈ L.sections n := fun a ↦ hV (e a).2
  let G : ℝ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ := fun s ↦
    gram (W₀.lerp W₁ s) dV n (fun a ↦ (e a : Fin A.n → X → ℂ))
  let G' : ℝ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ := fun s ↦ Matrix.of fun a b ↦
    ∫ x, ((-(n : ℝ) * u x : ℝ) : ℂ) *
      ptInner (W₀.lerp W₁ s) n (e a : Fin A.n → X → ℂ) (e b) x ∂dV.μ
  have hpos : ∀ s, (G s).PosDef := fun s ↦ gram_posDef (W₀.lerp W₁ s) dV hV e
  have hder : ∀ s a b, HasDerivAt (fun r ↦ G r a b) (G' s a b) s := by
    intro s a b
    have hG : (fun r ↦ G r a b) = fun r ↦ ∫ x, ptInner W₀ n (e a : Fin A.n → X → ℂ) (e b) x *
        ((Real.exp (-(n : ℝ) * r * u x) : ℝ) : ℂ) ∂dV.μ := by
      funext r
      simp only [G, gram, Matrix.of_apply]
      congr 1
      funext x
      exact ptInner_lerp W₀ W₁ n _ _ r x
    rw [hG]
    refine (hasDerivAt_integral_exp (μ := dV.μ) (continuous_ptInner W₀ (hE a) (hE b)) hu
      (-(n : ℝ)) s).congr_deriv ?_
    simp only [G', Matrix.of_apply]
    congr 1
    funext x
    rw [ptInner_lerp]
    push_cast
    ring
  have h := LogDetDerivative.intersectionNumber_baseChange (Module.finrank ℂ V) G G' hpos hder t
  have htr : ((G t)⁻¹ * G' t).trace =
      ∫ x, ((-(n : ℝ) * u x : ℝ) : ℂ) * (bergman (W₀.lerp W₁ t) dV V n x : ℂ) ∂dV.μ :=
    trace_eq (W₀.lerp W₁ t) dV hV e _ (Complex.continuous_ofReal.comp (continuous_const.mul hu))
  refine h.congr_deriv ?_
  rw [htr]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
