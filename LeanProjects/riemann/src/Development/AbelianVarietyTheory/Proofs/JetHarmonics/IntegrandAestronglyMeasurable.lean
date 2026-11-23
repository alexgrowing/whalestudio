import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace GlobalTheory.RegularisedIntegral

open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SqIntegrable (D : RealPlaceData k r Wp Wq) (α : ℝ) : Prop :=
  0 ≤ α ∧ Integrable (fun g : Mt k r =>
    gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α)) D.μG

variable {D : RealPlaceData k r Wp Wq} {α : ℝ}

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem SqIntegrable.integrable (H : SqIntegrable D α) : Integrable (fun g : Mt k r =>
    gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α)) D.μG := H.2

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in

theorem sqIntegrable_of_threshold (D : RealPlaceData k r Wp Wq) (hα : AB k r ≤ α) : SqIntegrable D α := by
  have h0 : 0 ≤ α := le_trans (P.B2.AB_nonneg k r) hα
  refine ⟨h0, ?_⟩
  have hfin := norm_power_integrable_sharp k r D.μG α D.haarG hα
  have hm : Measurable fun g : Mt k r => gN (Matrix.of g : Mat k r) ^ (-α) :=
    (show Continuous fun g : Mt k r => gN (Matrix.of g : Mat k r) from gN_continuous).measurable.pow_const _
  have hnn : ∀ g : Mt k r, 0 ≤ gN (Matrix.of g : Mat k r) ^ (-α) := fun g => Real.rpow_nonneg (gN_nonneg _) _
  have hI : Integrable (fun g : Mt k r => gN (Matrix.of g : Mat k r) ^ (-α)) D.μG :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)).2 hfin⟩
  refine hI.mono' (hm.mul hm).aestronglyMeasurable ?_
  filter_upwards [haar_ae D.haarG] with g hg
  rw [Real.norm_of_nonneg (mul_nonneg (hnn g) (hnn g))]
  exact mul_le_of_le_one_right (hnn g)
    (Real.rpow_le_one_of_one_le_of_nonpos (matrix_norm_ge_one k r _ hg) (by linarith))

theorem integrand_aestronglyMeasurable (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    AEStronglyMeasurable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  have hxy := inSS_mem D hp
  have hAt : AEStronglyMeasurable (fun g : Mt k r => A (sgs p (Matrix.of g))) D.μG := by
    simp only [sgs_eq]
    exact admissible_ae_strongly_measurable (admissible_two_sided_translate H.1 hA (WeylGroupFacts.uh_inv hxy.1) hxy.2) D.haarG
  have h1 : AEStronglyMeasurable (fun g : Mt k r => Sd D p (A (sgs p (Matrix.of g)))) D.μG :=
    (Sd D p).continuous.comp_aestronglyMeasurable hAt
  exact hsInner_continuous.comp_aestronglyMeasurable (h1.prodMk (admissible_ae_strongly_measurable hB D.haarG))

theorem integrand_norm_le (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) {g : Mat k r} (hg : g ∈ GV k r) {M : ℝ} (hM : normProductOfPair p ≤ M) :
    ‖hsInner (rho D p A g) (B g)‖ ≤
      (Module.finrank ℂ Wq : ℝ) * (cA * M ^ α * cB) * (gN g ^ (-α) * gN g ^ (-α)) := by
  have hxy := inSS_mem D hp
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  have h1 := admissible_norm_bound (admissible_two_sided_translate H.1 hA (WeylGroupFacts.uh_inv hxy.1) hxy.2) hg
  rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hxy.1)] at h1
  have h2 := admissible_norm_bound hB hg
  have h3 : (gN (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r) *
      gN (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹) ^ α ≤ M ^ α :=
    Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _)) hM H.1
  have hg0 : 0 ≤ gN g ^ (-α) := Real.rpow_nonneg (gN_nonneg g) _
  have hM0 : 0 ≤ M ^ α := le_trans (Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _) h3
  refine (hilbert_schmidt_integrand_bound D A B hp g).trans ?_
  calc (Module.finrank ℂ Wq : ℝ) * (‖A ((Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ * g *
        (Matrix.of p.2.2 * Matrix.of p.2.1))‖ * ‖B g‖)
      ≤ (Module.finrank ℂ Wq : ℝ) * ((cA * M ^ α * gN g ^ (-α)) * (cB * gN g ^ (-α))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity))
          (by positivity)
        gcongr
    _ = _ := by ring

theorem coef_integrand_integrable (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : admitted α cA A) (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    Integrable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  refine (H.integrable.const_mul ((Module.finrank ℂ Wq : ℝ) * (cA * normProductOfPair p ^ α * cB))).mono'
    (integrand_aestronglyMeasurable H hA hB hp) ?_
  filter_upwards [haar_ae D.haarG] with g hg
  exact integrand_norm_le H hA hB hp hg le_rfl

theorem coef_continuousOn (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) : ContinuousOn (Ph D A B) {p | D.inSS p} := by
  intro p₀ hp₀
  show ContinuousWithinAt (fun p => ∫ g : Mt k r, hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g)) ∂D.μG)
    {p | D.inSS p} p₀
  refine continuousWithinAt_of_dominated
    (bound := fun g : Mt k r => (Module.finrank ℂ Wq : ℝ) * (cA * (normProductOfPair p₀ + 1) ^ α * cB) *
      (gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α))) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact integrand_aestronglyMeasurable H hA hB hp
  · have hN : ∀ᶠ p in 𝓝[{p | D.inSS p}] p₀, normProductOfPair p < normProductOfPair p₀ + 1 :=
      (norm_product_continuous_on D p₀ hp₀).tendsto.eventually_lt_const (lt_add_one _)
    filter_upwards [self_mem_nhdsWithin, hN] with p hp hNp
    filter_upwards [haar_ae D.haarG] with g hg
    exact integrand_norm_le H hA hB hp hg hNp.le
  · exact (SqIntegrable.integrable H).const_mul _
  · filter_upwards [haar_ae D.haarG] with g hg
    have h1 : ContinuousWithinAt (fun p : SS k r => A (sgs p (Matrix.of g))) {p | D.inSS p} p₀ :=
      (hA.1.comp (conjugated_pair_continuous_on D (Matrix.of g)) (fun p hp => conj_product_mem_unitary_group D hp hg)) p₀ hp₀
    have h2 : ContinuousWithinAt (fun p : SS k r => Sd D p (A (sgs p (Matrix.of g)))) {p | D.inSS p} p₀ :=
      (Sd_continuousOn D p₀ hp₀).clm_apply h1
    exact hsInner_continuous.continuousAt.comp_continuousWithinAt (h2.prodMk continuousWithinAt_const)

theorem coef_dilate (_H : SqIntegrable D α) (A B : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Ph D A B (dilation₂ (x, y) p) =
      Ph D (fun g => A (aDil k r x * g * (aDil k r y)⁻¹)) (fun g => B (aDil k r x * g * (aDil k r y)⁻¹)) p := by
  have hax := aDil_mem k r hx
  have hay := aDil_inv_mem k r hy
  have mpL : MeasurePreserving (lmulM (aDil k r x)) D.μG D.μG :=
    ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarG.left _ hax⟩
  have mpR : MeasurePreserving (rmulF (aDil k r y)⁻¹) D.μG D.μG :=
    ⟨(continuous_right_multiplication_map _).measurable, D.haarG.right _ hay⟩
  have eL : MeasurableEmbedding (lmulM (k := k) (r := r) (aDil k r x)) :=
    (BesselUnitaryEquiv.lmulE _ (WeylGroupFacts.isUnit_of_uh hax)).measurableEmbedding
  have eR : MeasurableEmbedding (rmulF (aDil k r y)⁻¹) :=
    (rightMulMeasurableEquiv _ (WeylGroupFacts.isUnit_of_uh hay)).measurableEmbedding
  unfold Ph
  rw [← (mpR.comp mpL).integral_comp (eR.comp eL)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have e : (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g) : Mat k r) =
      aDil k r x * Matrix.of g * (aDil k r y)⁻¹ := rfl
  show hsInner (rho D (dilation₂ (x, y) p) A (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g)))
      (B (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g))) =
    hsInner (rho D p (fun g => A (aDil k r x * g * (aDil k r y)⁻¹)) (Matrix.of g))
      (B (aDil k r x * Matrix.of g * (aDil k r y)⁻¹))
  rw [e, rho_eq, rho_eq, sgs_dil P.dilation_unipotent_weyl_measure D hp hx hy, Sd_dil]

theorem coef_hasDerivAt (H : SqIntegrable D α) {A B A1 B1 : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : admitted α cA A) (hA1 : admitted α cA A1) (hB : admitted α cB B) (hB1 : admitted α cB B1)
    {p : SS k r} (hp : D.inSS p) {a b : ℝ → Mat k r} {κ : ℝ → ℝ} {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    {K : ℝ} (ha : ∀ t ∈ s, a t ∈ GV k r) (hb : ∀ t ∈ s, b t ∈ GV k r)
    (hKa : ∀ t ∈ s, gN (a t)⁻¹ ≤ K) (hKb : ∀ t ∈ s, gN (b t)⁻¹ ≤ K) (hκ : ∀ t ∈ s, |κ t| ≤ K)
    (dA : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => A (a t * z * b t)) (κ t • A1 (a t * z * b t)) t)
    (dB : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => B (a t * z * b t)) (κ t • B1 (a t * z * b t)) t) :
    HasDerivAt (fun t => Ph D (fun g => A (a t * g * b t)) (fun g => B (a t * g * b t)) p)
      ((κ t₀ : ℂ) * (Ph D (fun g => A1 (a t₀ * g * b t₀)) (fun g => B (a t₀ * g * b t₀)) p +
        Ph D (fun g => A (a t₀ * g * b t₀)) (fun g => B1 (a t₀ * g * b t₀)) p)) t₀ := by
  have hα := H.1
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  obtain ⟨hS1, hS2⟩ := inSS_mem D hp
  have hS1i := WeylGroupFacts.uh_inv hS1
  have hK0 : 0 ≤ K := le_trans (gN_nonneg _) (hKa t₀ ht₀)
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  obtain ⟨S1, hS1d⟩ : ∃ S1 : Mat k r, S1 = (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ := ⟨_, rfl⟩
  obtain ⟨S2, hS2d⟩ : ∃ S2 : Mat k r, S2 = (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) := ⟨_, rfl⟩
  rw [← hS1d] at hS1i
  rw [← hS2d] at hS2
  have hsgs : ∀ g : Mat k r, sgs p g = S1 * g * S2 := by
    intro g; rw [sgs_eq, hS1d, hS2d]
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = (K * K) ^ α := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = (gN S1⁻¹ * gN S2⁻¹) ^ α := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPd]; exact Real.rpow_nonneg (mul_nonneg hK0 hK0) _
  have hM0 : 0 ≤ M := by rw [hMd]; exact Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _
  have hG := haar_ae D.haarG

  have ms2 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ t ∈ s,
      AEStronglyMeasurable (fun g : Mt k r => f (a t * sgs p (Matrix.of g) * b t)) D.μG := by
    intro f c hf t ht
    have := admissible_ae_strongly_measurable (admissible_two_sided_translate hα (admissible_two_sided_translate hα hf (ha t ht) (hb t ht)) hS1i hS2) D.haarG
    simpa only [hsgs] using this
  have ms1 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ t ∈ s,
      AEStronglyMeasurable (fun g : Mt k r => f (a t * Matrix.of g * b t)) D.μG := by
    intro f c hf t ht
    exact admissible_ae_strongly_measurable (admissible_two_sided_translate hα hf (ha t ht) (hb t ht)) D.haarG

  have b2 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ g : Mt k r,
      (Matrix.of g : Mat k r) ∈ GV k r → ∀ t ∈ s,
      ‖f (a t * sgs p (Matrix.of g) * b t)‖ ≤ c * P * M * gN (Matrix.of g : Mat k r) ^ (-α) := by
    intro f c hf g hg t ht
    rw [hsgs, hPd, hMd]
    exact translated_norm_bound hα hf (ha t ht) (hb t ht) hS1i hS2 hg (hKa t ht) (hKb t ht)
  have b1 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ g : Mt k r,
      (Matrix.of g : Mat k r) ∈ GV k r → ∀ t ∈ s,
      ‖f (a t * Matrix.of g * b t)‖ ≤ c * P * 1 * gN (Matrix.of g : Mat k r) ^ (-α) := by
    intro f c hf g hg t ht
    rw [hPd, mul_one]
    exact norm_admissible_of_double_translate_le hα hf (ha t ht) (hb t ht) hg (hKa t ht) (hKb t ht)
  have hm0 : ∀ g : Mt k r, 0 ≤ gN (Matrix.of g : Mat k r) ^ (-α) := fun g => Real.rpow_nonneg (gN_nonneg _) _
  have key := parametric_derivative_under_integral (μ := D.μG) (Sd D p) (Sd_norm_le D hp)
    (u := fun t g => A (a t * sgs p (Matrix.of g) * b t)) (v := fun t g => B (a t * Matrix.of g * b t))
    (u' := fun t g => κ t • A1 (a t * sgs p (Matrix.of g) * b t))
    (v' := fun t g => κ t • B1 (a t * Matrix.of g * b t))
    hs (m := fun g => gN (Matrix.of g : Mat k r) ^ (-α)) (C := (1 + K) * (cA + cB) * P * (1 + M))
    (SqIntegrable.integrable H) (ms2 hA) (ms1 hB) (fun t ht => (ms2 hA1 t ht).const_smul (κ t))
    (fun t ht => (ms1 hB1 t ht).const_smul (κ t))
    (by
      filter_upwards [hG] with g hg t ht
      have hz : sgs p (Matrix.of g) ∈ GV k r := by
        rw [hsgs]; exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hS1i hg) hS2
      exact dA _ hz t ht)
    (by
      filter_upwards [hG] with g hg t ht
      exact dB _ hg t ht)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b2 hA g hg t ht
      have h2 := product_bound_monotone_factors_le (e := 1) (K := K) (c₀ := cA + cB) (M := M) zero_le_one (by linarith) hcA
        (by linarith) hP0 hM0 (by linarith) (hm0 g)
      linarith)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b1 hB g hg t ht
      have h2 := product_bound_monotone_factors_le (e := 1) (K := K) (c₀ := cA + cB) (M := M) zero_le_one (by linarith) hcB
        (by linarith) hP0 zero_le_one (by linarith) (hm0 g)
      linarith)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b2 hA1 g hg t ht
      have h2 := product_bound_monotone_factors_le (e := |κ t|) (K := K) (c₀ := cA + cB) (M := M) (abs_nonneg _)
        (by have := hκ t ht; linarith) hcA (by linarith) hP0 hM0 (by linarith) (hm0 g)
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg _)) h2)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b1 hB1 g hg t ht
      have h2 := product_bound_monotone_factors_le (e := |κ t|) (K := K) (c₀ := cA + cB) (M := M) (abs_nonneg _)
        (by have := hκ t ht; linarith) hcB (by linarith) hP0 zero_le_one (by linarith) (hm0 g)
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg _)) h2)
  have i1 := coef_integrand_integrable H (admissible_two_sided_translate hα hA1 (ha t₀ ht₀) (hb t₀ ht₀))
    (admissible_two_sided_translate hα hB (ha t₀ ht₀) (hb t₀ ht₀)) hp
  have i2 := coef_integrand_integrable H (admissible_two_sided_translate hα hA (ha t₀ ht₀) (hb t₀ ht₀))
    (admissible_two_sided_translate hα hB1 (ha t₀ ht₀) (hb t₀ ht₀)) hp
  have e1 : (∫ g : Mt k r, (hsInner (Sd D p (κ t₀ • A1 (a t₀ * sgs p (Matrix.of g) * b t₀)))
        (B (a t₀ * Matrix.of g * b t₀)) +
      hsInner (Sd D p (A (a t₀ * sgs p (Matrix.of g) * b t₀))) (κ t₀ • B1 (a t₀ * Matrix.of g * b t₀))) ∂D.μG) =
      (κ t₀ : ℂ) * (Ph D (fun g => A1 (a t₀ * g * b t₀)) (fun g => B (a t₀ * g * b t₀)) p +
        Ph D (fun g => A (a t₀ * g * b t₀)) (fun g => B1 (a t₀ * g * b t₀)) p) := by
    unfold Ph
    rw [← integral_add i1 i2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [rho_eq]
    rw [← Complex.coe_smul (κ t₀) (A1 _), ← Complex.coe_smul (κ t₀) (B1 _), map_smul, hsInner_smul_left,
      hsInner_smul_right, Complex.conj_ofReal]
    ring
  rw [← e1]
  have e2 : (fun t => Ph D (fun g => A (a t * g * b t)) (fun g => B (a t * g * b t)) p) =
      fun t => ∫ g : Mt k r, hsInner (Sd D p (A (a t * sgs p (Matrix.of g) * b t)))
        (B (a t * Matrix.of g * b t)) ∂D.μG := by
    funext t
    unfold Ph
    simp only [rho_eq]
  rw [e2]
  exact key

theorem coef_hasDerivAt_right (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Rr A)) (hB : admitted α cB B) (hB' : admitted α cB (Rr B)) (dA : DR A) (dB : DR B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => Ph D A B (dilation₂ (x, y') p))
      (((-(rr r / y) : ℝ) : ℂ) * (Ph D (Rr A) B (dilation₂ (x, y) p) + Ph D A (Rr B) (dilation₂ (x, y) p))) y := by
  obtain ⟨K1, hK1, hK1b⟩ := aDil_gN_bound k r (a := y / 2) (b := 2 * y) (by linarith)
  have hs : Set.Ioo (y / 2) (2 * y) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Set.Ioo (y / 2) (2 * y), 0 < t := fun t ht => by have := ht.1; linarith
  have hr := rr_pos r
  have hd : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)}, DR f → ∀ z ∈ GV k r, ∀ t ∈ Set.Ioo (y / 2) (2 * y),
      HasDerivAt (fun t => f (aDil k r x * z * (aDil k r t)⁻¹))
        ((-(rr r / t)) • Rr f (aDil k r x * z * (aDil k r t)⁻¹)) t := by
    intro f df z hz t ht
    exact curveR f (aDil k r x * z) (hpos t ht)
      (df _ (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (aDil_mem k r hx) hz) (aDil_inv_mem k r (hpos t ht))))
  have key := coef_hasDerivAt H hA hA' hB hB' hp (a := fun _ => aDil k r x) (b := fun t => (aDil k r t)⁻¹)
    (κ := fun t => -(rr r / t)) hs (K := K1 + gN (aDil k r x)⁻¹ + 2 * rr r / y)
    (fun t _ => aDil_mem k r hx) (fun t ht => aDil_inv_mem k r (hpos t ht))
    (fun t _ => by
      have h1 : 0 ≤ 2 * rr r / y := by positivity
      linarith)
    (fun t ht => by
      have h1 : 0 ≤ 2 * rr r / y := by positivity
      have h2 := gN_nonneg (aDil k r x)⁻¹
      have h3 := (hK1b t ⟨ht.1.le, ht.2.le⟩).1
      rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh (aDil_mem k r (hpos t ht)))]
      linarith)
    (fun t ht => by
      have h2 := gN_nonneg (aDil k r x)⁻¹
      have h3 : |-(rr r / t)| ≤ 2 * rr r / y := by
        rw [abs_neg, abs_of_pos (div_pos hr (hpos t ht)), div_le_div_iff₀ (hpos t ht) hy]
        have := ht.1
        nlinarith
      linarith)
    (hd dA) (hd dB)
  rw [coef_dilate H (Rr A) B hp hx hy, coef_dilate H A (Rr B) hp hx hy]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact coef_dilate H A B hp hx (hpos t ht)

theorem coef_hasDerivAt_left (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Ll A)) (hB : admitted α cB B) (hB' : admitted α cB (Ll B)) (dA : DL A) (dB : DL B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => Ph D A B (dilation₂ (x', y) p))
      (((-(rr r / x) : ℝ) : ℂ) * (Ph D (Ll A) B (dilation₂ (x, y) p) + Ph D A (Ll B) (dilation₂ (x, y) p))) x := by
  obtain ⟨K1, hK1, hK1b⟩ := aDil_gN_bound k r (a := x / 2) (b := 2 * x) (by linarith)
  have hs : Set.Ioo (x / 2) (2 * x) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Set.Ioo (x / 2) (2 * x), 0 < t := fun t ht => by have := ht.1; linarith
  have hr := rr_pos r
  have hd : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)}, DL f → ∀ z ∈ GV k r, ∀ t ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun t => f (aDil k r t * z * (aDil k r y)⁻¹))
        ((-(rr r / t)) • Ll f (aDil k r t * z * (aDil k r y)⁻¹)) t := by
    intro f df z hz t ht
    have h := curveL f (z * (aDil k r y)⁻¹) (hpos t ht)
      (df _ (WeylGroupFacts.uh_mul (aDil_mem k r (hpos t ht)) (WeylGroupFacts.uh_mul hz (aDil_inv_mem k r hy))))
    simpa only [Matrix.mul_assoc] using h
  have key := coef_hasDerivAt H hA hA' hB hB' hp (a := fun t => aDil k r t) (b := fun _ => (aDil k r y)⁻¹)
    (κ := fun t => -(rr r / t)) hs (K := K1 + gN ((aDil k r y)⁻¹)⁻¹ + 2 * rr r / x)
    (fun t ht => aDil_mem k r (hpos t ht)) (fun t _ => aDil_inv_mem k r hy)
    (fun t ht => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 := (hK1b t ⟨ht.1.le, ht.2.le⟩).2
      linarith)
    (fun t _ => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      linarith)
    (fun t ht => by
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 : |-(rr r / t)| ≤ 2 * rr r / x := by
        rw [abs_neg, abs_of_pos (div_pos hr (hpos t ht)), div_le_div_iff₀ (hpos t ht) hx]
        have := ht.1
        nlinarith
      linarith)
    (hd dA) (hd dB)
  rw [coef_dilate H (Ll A) B hp hx hy, coef_dilate H A (Ll B) hp hx hy]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact coef_dilate H A B hp (hpos t ht) hy

theorem leibnizR_hasDerivAt_right (H : SqIntegrable D α) {l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA (l + 1) 0 A) (hB : AdmW α cB (l + 1) 0 B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => QR D p 0 l A B x y') (((-(rr r / y) : ℝ) : ℂ) * QR D p 0 (l + 1) A B x y) y := by
  induction l generalizing A B with
  | zero =>
    exact coef_hasDerivAt_right H (hA.1 0 (by omega) 0 le_rfl) (hA.1 1 le_rfl 0 le_rfl) (hB.1 0 (by omega) 0 le_rfl)
      (hB.1 1 le_rfl 0 le_rfl) (hA.2.1 0 (by omega)) (hB.2.1 0 (by omega)) hp hx hy
  | succ l ih =>
    have h1 := ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)
    have h2 := ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3

theorem leibnizL_hasDerivAt_left (H : SqIntegrable D α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 (m + 1) A) (hB : AdmW α cB 0 (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QL D p m A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QL D p (m + 1) A B x y) x := by
  induction m generalizing A B with
  | zero =>
    exact coef_hasDerivAt_left H (hA.1 0 le_rfl 0 (by omega)) (hA.1 0 le_rfl 1 le_rfl) (hB.1 0 le_rfl 0 (by omega))
      (hB.1 0 le_rfl 1 le_rfl) (hA.2.2 0 le_rfl 0 (by omega)) (hB.2.2 0 le_rfl 0 (by omega)) hp hx hy
  | succ m ih =>
    have h1 := ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)
    have h2 := ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3

theorem leibnizR_hasDerivAt_left (H : SqIntegrable D α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l (m + 1) A) (hB : AdmW α cB l (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QR D p m l A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QR D p (m + 1) l A B x y) x := by
  induction l generalizing A B with
  | zero => exact leibnizL_hasDerivAt_left H hA hB hp hx hy
  | succ l ih =>
    have h1 := ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)
    have h2 := ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3

theorem leibnizL_continuousOn (H : SqIntegrable D α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 m A) (hB : AdmW α cB 0 m B) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => QL D q.1 m A B q.2.1 q.2.2) ({p | D.inSS p} ×ˢ Quad) := by
  induction m generalizing A B with
  | zero =>
    have h1 := coef_continuousOn H (admissible_of_weighted hA) (admissible_of_weighted hB)
    have h2 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => dilation₂ q.2 q.1) ({p | D.inSS p} ×ˢ Quad) :=
      (dilationAction_continuousOn k r).mono (Set.prod_mono (Set.subset_univ _) le_rfl)
    refine h1.comp h2 ?_
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact dil_inSS P.dilation_unipotent_measure D hp ht.1 ht.2
  | succ m ih => exact (ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)).add (ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB))

theorem leibnizR_continuousOn (H : SqIntegrable D α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l m A) (hB : AdmW α cB l m B) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => QR D q.1 m l A B q.2.1 q.2.2) ({p | D.inSS p} ×ˢ Quad) := by
  induction l generalizing A B with
  | zero => exact leibnizL_continuousOn H hA hB
  | succ l ih => exact (ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)).add (ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB))

theorem leibnizR_continuousOn_param (H : SqIntegrable D α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l m A) (hB : AdmW α cB l m B) {p : SS k r} (hp : D.inSS p) :
    ContinuousOn (fun t : ℝ × ℝ => QR D p m l A B t.1 t.2) Quad :=
  (leibnizR_continuousOn H hA hB).comp (Continuous.prodMk_right p).continuousOn (fun _ ht => ⟨hp, ht⟩)

theorem bracket_calculus (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {p : SS k r} (hp : D.inSS p) :
    (∀ x y, oneMinusDD (regBracket D F F' p) x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam (rr r) (Wd D) m x * gam (rr r) (Wd D) l y : ℝ) : ℂ) * QR D p m l F F' x y) ∧
    (∀ x, ContDiff ℝ 2 (fun y => regBracket D F F' p x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => regBracket D F F' p x y -
      iteratedDeriv 2 (fun y' => regBracket D F F' p x y') y)) ∧
    (∀ x₁ x₂ : ℝ, (∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
          Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) :=
  al2 (Wd_contDiff D) (Wd_tsupport D) (rr r) (fun m l x y => QR D p m l F F' x y)
    (fun l hl x hx y hy => leibnizR_hasDerivAt_right H (admissibleWeight_mono hF (by omega) (by omega))
      (admissibleWeight_mono hF' (by omega) (by omega)) hp hx hy)
    (fun m hm l hl x hx y hy => leibnizR_hasDerivAt_left H (admissibleWeight_mono hF hl (by omega))
      (admissibleWeight_mono hF' hl (by omega)) hp hx hy)
    (fun m hm l hl => leibnizR_continuousOn_param H (admissibleWeight_mono hF hl hm) (admissibleWeight_mono hF' hl hm) hp)
    (regBracket D F F' p) (regBracket_eq D F F' p)

theorem cutBracket_measurable (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') : StronglyMeasurable (Bt D F F') := by
  refine stronglyMeasurable_indicator_of_continuousOn' ((measurableSet_inSS D).prod (measurableSet_Ioi.prod measurableSet_Ioi)) ?_
  have e : (fun q : SS k r × (ℝ × ℝ) => regBracket D F F' q.1 q.2.1 q.2.2) =
      fun q => ((Wd D q.2.1 * Wd D q.2.2 : ℝ) : ℂ) * QR D q.1 0 0 F F' q.2.1 q.2.2 :=
    funext fun q => regBracket_eq D F F' q.1 q.2.1 q.2.2
  rw [e]
  exact ((cutoff_square_product_continuous D).comp continuous_snd).continuousOn.mul
    (leibnizR_continuousOn H (admissibleWeight_mono hF (by omega) (by omega)) (admissibleWeight_mono hF' (by omega) (by omega)))

end GlobalTheory.RegularisedIntegral
