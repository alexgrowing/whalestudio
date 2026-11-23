import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
import GroundTheory.AutomorphicForms.RealGroupsHaar
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL.HaarDom

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem isOpenEmbedding_valG (n : ℕ) : Topology.IsOpenEmbedding (Units.val : G n → Mat n) :=
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def coords {n : ℕ} (M : Mat n) : Idx n → ℝ :=
  fun p => if p.1 then (M p.2.1 p.2.2).re else (M p.2.1 p.2.2).im

theorem cm_apply {n : ℕ} (t : Idx n → ℝ) (i j : Fin n) :
    cm t i j = (t (true, i, j) : ℂ) + (t (false, i, j) : ℂ) * Complex.I := by
  simp only [cm, bs, Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  have key : ∀ f : Fin n → Fin n → ℂ, (∑ x, ∑ y, if x = i ∧ y = j then f x y else 0) = f i j := by
    intro f
    simp [ite_and, Finset.sum_ite_eq']
  simp [Matrix.single_apply, Finset.sum_add_distrib, key]

def cmE (n : ℕ) : (Idx n → ℝ) ≃ₗ[ℝ] Mat n where
  toFun := cm
  map_add' s t := by simp [cm, add_smul, Finset.sum_add_distrib]
  map_smul' c t := by simp [cm, mul_smul, Finset.smul_sum]
  invFun := coords
  left_inv t := by
    funext ⟨b, i, j⟩
    cases b <;> simp [coords, cm_apply]
  right_inv M := by
    ext i j
    simp [coords, cm_apply, Complex.re_add_im]

instance locallyCompactSpace_G (n : ℕ) : LocallyCompactSpace (G n) :=
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (isOpenEmbedding_valG n).locallyCompactSpace
instance secondCountableTopology_G (n : ℕ) : SecondCountableTopology (G n) :=
  haveI : SecondCountableTopology (Mat n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  (isOpenEmbedding_valG n).isEmbedding.secondCountableTopology

def aH (n : ℕ) : (Idx n → ℝ) ≃ₜ Mat n :=
  (cmE n).toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft (1 : Mat n))

open scoped GroundTheory.Automorphic ENNReal

def mu0 (n : ℕ) : Measure (Mat n) := Measure.map (cmE n) volume

instance isAddHaarMeasure_pushforward (n : ℕ) : (mu0 n).IsAddHaarMeasure :=
  (cmE n).toContinuousLinearEquiv.isAddHaarMeasure_map volume

theorem map_aH (n : ℕ) : Measure.map (aH n) volume = mu0 n := by
  have h1 : Measurable (cmE n) := (cmE n).toContinuousLinearEquiv.continuous.measurable
  have h2 : Measurable (fun x : Mat n => (1 : Mat n) + x) := (continuous_const.add continuous_id).measurable
  have : (aH n : (Idx n → ℝ) → Mat n) = (fun x : Mat n => (1 : Mat n) + x) ∘ (cmE n) := rfl
  rw [this, ← Measure.map_map h2 h1]
  exact map_add_left_eq_self (mu0 n) 1

theorem lint_chart {n : ℕ} (g : Mat n → ℝ≥0∞) (Q : Set (Idx n → ℝ)) :
    ∫⁻ t in Q, g (1 + cm t) = ∫⁻ x in aH n '' Q, g x ∂(mu0 n) := by
  have hemb := (aH n).measurableEmbedding
  rw [← map_aH, hemb.restrict_map, hemb.lintegral_map,
    Set.preimage_image_eq _ (aH n).injective]
  rfl

theorem lint_haar {n : ℕ} (g : Mat n → ℝ≥0∞) (S : Set (G n)) (hS : MeasurableSet S) :
    ∫⁻ y in S, g y.val ∂(GroundTheory.Automorphic.haarGLComplex (mu0 n)) =
      ∫⁻ x in Units.val '' S, GroundTheory.Automorphic.haarDensityGLComplex x * g x ∂(mu0 n) := by
  have hemb := GroundTheory.Automorphic.measurableEmbedding_val_GLComplex (n := Fin n)
  have hV : Measure.map Units.val ((GroundTheory.Automorphic.haarGLComplex (mu0 n)).restrict S) =
      ((mu0 n).restrict (Units.val '' S)).withDensity GroundTheory.Automorphic.haarDensityGLComplex := by
    have hVm : MeasurableSet (Units.val '' S) := hemb.measurableSet_image.2 hS
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Measure.restrict_apply (hemb.measurable hs),
      GroundTheory.Automorphic.haarGLComplex_apply, ← restrict_withDensity hVm,
      Measure.restrict_apply hs, Set.image_preimage_inter]
  rw [← hemb.lintegral_map, hV,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      GroundTheory.Automorphic.measurable_haarDensityGLComplex
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  rfl

theorem lint_core {n : ℕ} (g : Mat n → ℝ≥0∞) (Q : Set (Idx n → ℝ)) (S : Set (G n)) (hS : IsCompact S)
    (h : ∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) (B : ℝ) (hB0 : 0 < B)
    (hB : ∀ y ∈ S, (‖(y : Mat n).det‖ ^ 2) ^ n ≤ B) :
    ∫⁻ t in Q, g (1 + cm t) ≤
      ENNReal.ofReal B * ∫⁻ y in S, g y.val ∂(GroundTheory.Automorphic.haarGLComplex (mu0 n)) := by
  have hV : MeasurableSet (Units.val '' S) :=
    (hS.image Units.continuous_val).isClosed.measurableSet
  rw [lint_chart, lint_haar g S hS.measurableSet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ x in aH n '' Q, g x ∂(mu0 n) ≤ ∫⁻ x in Units.val '' S, g x ∂(mu0 n) := by
        refine lintegral_mono_set ?_
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨y, hy, e⟩ := h t ht
        exact ⟨y, hy, e⟩
    _ ≤ _ := by
        refine setLIntegral_mono' hV ?_
        rintro _ ⟨y, hy, rfl⟩
        have hd : (y : Mat n).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
        have hpos : 0 < (‖(y : Mat n).det‖ ^ 2) ^ n := by positivity
        have h1 : 1 ≤ ENNReal.ofReal B * GroundTheory.Automorphic.haarDensityGLComplex (y : Mat n) := by
          rw [GroundTheory.Automorphic.haarDensityGLComplex, ← ENNReal.ofReal_mul hB0.le,
            ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Fintype.card_fin, inv_pow, ← div_eq_mul_inv, one_le_div hpos]
          exact hB y hy
        calc g y.val = 1 * g y.val := (one_mul _).symm
          _ ≤ (ENNReal.ofReal B * GroundTheory.Automorphic.haarDensityGLComplex (y : Mat n)) * g y.val := by
              gcongr
          _ = _ := mul_assoc _ _ _

theorem dom_units (n : ℕ) (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)) (hQ : IsCompact Q) (hS : IsCompact S)
    (h : ∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  have hH := Measure.isMulLeftInvariant_eq_smul (GroundTheory.Automorphic.haarGLComplex (mu0 n)) μ
  set κ := Measure.haarScalarFactor (GroundTheory.Automorphic.haarGLComplex (mu0 n)) μ with hκ
  have hcont : Continuous (fun y : G n => (‖(y : Mat n).det‖ ^ 2) ^ n) :=
    (((Units.continuous_val.matrix_det).norm.pow _).pow _)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  have hB1 : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB2 : ∀ y ∈ S, (‖(y : Mat n).det‖ ^ 2) ^ n ≤ max B 1 := fun y hy =>
    ((le_abs_self _).trans (by simpa using hB y hy)).trans (le_max_left _ _)
  refine ⟨max B 1 * κ, by positivity, fun φ hφ h0 => ?_⟩
  have hmem : ∀ y : G n, (y : Mat n) ∈ GLs n := fun y =>
    ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hf : Continuous (fun y : G n => φ y.val) :=
    hφ.comp_continuous Units.continuous_val hmem
  have hint2 : IntegrableOn (fun y : G n => φ y.val) S μ := hf.continuousOn.integrableOn_compact hS
  have hint1 : IntegrableOn (fun t => φ (1 + cm t)) Q := by
    refine ContinuousOn.integrableOn_compact hQ ?_
    refine hφ.comp (aH n).continuous.continuousOn ?_
    intro t ht
    obtain ⟨y, _, e⟩ := h t ht
    show 1 + cm t ∈ GLs n
    rw [← e]
    exact hmem y
  have key := lint_core (fun x => ENNReal.ofReal (φ x)) Q S hS h (max B 1) hB1 hB2
  rw [hH, Measure.restrict_smul, lintegral_smul_measure,
    ← ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun _ => h0 _),
    ← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun _ => h0 _)] at key
  have hR : 0 ≤ ∫ y in S, φ y.val ∂μ := integral_nonneg fun _ => h0 _
  have e : ENNReal.ofReal (max B 1) * κ • ENNReal.ofReal (∫ y in S, φ y.val ∂μ) =
      ENNReal.ofReal (max B 1 * κ * ∫ y in S, φ y.val ∂μ) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hB1.le, ENNReal.smul_def,
      ENNReal.ofReal_coe_nnreal, smul_eq_mul, mul_assoc]
  rw [e] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end GlobalTheory.CompanionTheory.SobGL.HaarDom

namespace GlobalTheory.CompanionTheory.SobGL

open scoped GroundTheory.Automorphic in

theorem lebesgue_le_haar :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)), IsCompact Q → IsCompact S → (∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  intro n m hB μ hμ Q S hQ hS h
  have e : m = Units.instMeasurableSpace :=
    hB.measurable_eq.trans (GroundTheory.Automorphic.borelSpace_GLComplex (n := Fin n)).measurable_eq.symm
  subst e
  exact HaarDom.dom_units n μ Q S hQ hS h

end GlobalTheory.CompanionTheory.SobGL
