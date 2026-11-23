import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PiScale

section Abstract

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R]
  [BorelSpace R] [SecondCountableTopology R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_mulVec_left (M : Matrix ι ι R) : Continuous (fun x : ι → R => M *ᵥ x) :=
  Continuous.matrix_mulVec continuous_const continuous_id

theorem image_mulVec_eq_preimage (M N : Matrix ι ι R) (h1 : M * N = 1) (h2 : N * M = 1)
    (s : Set (ι → R)) : (fun x => M *ᵥ x) '' s = (fun x => N *ᵥ x) ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Matrix.mulVec_mulVec, h2] using hx
  · intro hy
    exact ⟨N *ᵥ y, hy, by simp [Matrix.mulVec_mulVec, h1]⟩

theorem pi_image_mul (lf : Measure R) [SigmaFinite lf] (u v : ι → R) (huv : ∀ i, u i * v i = 1)
    (c : ι → ℝ≥0)
    (hc : ∀ i (s : Set R), MeasurableSet s → lf ((fun x => u i * x) '' s) = (c i : ℝ≥0∞) * lf s)
    (s : Set (ι → R)) (hs : MeasurableSet s) :
    (Measure.pi fun _ : ι => lf) ((fun x i => u i * x i) '' s) =
      (∏ i, (c i : ℝ≥0∞)) * (Measure.pi fun _ : ι => lf) s := by
  have hT : Measurable (fun (x : ι → R) i => v i * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have himg : (fun (x : ι → R) i => u i * x i) '' s = (fun (x : ι → R) i => v i * x i) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (fun i => v i * (u i * x i)) = x := by
        funext i
        rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
    · intro hy
      refine ⟨_, hy, ?_⟩
      funext i
      show u i * (v i * y i) = y i
      rw [← mul_assoc, huv, one_mul]
  have hpre : ∀ i (t : Set R), (fun x => v i * x) ⁻¹' t = (fun x => u i * x) '' t := by
    intro i t
    ext y
    constructor
    · intro hy
      exact ⟨_, hy, by simp only; rw [← mul_assoc, huv, one_mul]⟩
    · rintro ⟨x, hx, rfl⟩
      have : v i * (u i * x) = x := by rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
  have e1 : Measure.pi (fun i => c i • lf) =
      (Measure.pi fun _ : ι => lf).map (fun (x : ι → R) i => v i * x i) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi ht)]
    have : (fun (x : ι → R) i => v i * x i) ⁻¹' Set.pi Set.univ t =
        Set.pi Set.univ fun i => (fun x => u i * x) '' t i := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi, ← hpre]
    rw [this, Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hc i _ (ht i)]
    rfl
  have e2 : Measure.pi (fun i => c i • lf) =
      (∏ i, (c i : ℝ≥0∞)) • (Measure.pi fun _ : ι => lf) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
    rfl
  rw [himg, ← Measure.map_apply hT hs, ← e1, e2, Measure.smul_apply, smul_eq_mul]

theorem measurePreserving_transvection (lf : Measure R) [SigmaFinite lf] [lf.IsAddLeftInvariant]
    (i j : ι) (hij : i ≠ j) (c : R) :
    MeasurePreserving (fun x : ι → R => transvection i j c *ᵥ x)
      (Measure.pi fun _ : ι => lf) (Measure.pi fun _ : ι => lf) := by
  have ht : Measurable (fun x : ι → R => transvection i j c *ᵥ x) :=
    (continuous_mulVec_left _).measurable
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have hup : ∀ xi : R, transvection i j c *ᵥ Function.update x i xi =
      Function.update x i (xi + c * x j) := by
    intro xi
    funext k
    by_cases hk : k = i
    · subst hk
      simp [transvection, add_mulVec, single_mulVec, hij.symm]
    · simp [transvection, add_mulVec, single_mulVec, hk, hij.symm]
  simp only [Function.comp_apply, hup]
  exact lintegral_add_right_eq_self
    (fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)) (c * x j)

end Abstract

section Global

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Bf_mul (g h : Matrix ι ι F) : Bf (g * h) = Bf g * Bf h := by
  simp [Bf, Matrix.map_mul]

theorem Bf_one : Bf (1 : Matrix ι ι F) = 1 := by
  simp [Bf]

theorem Bf_inv_mul (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g⁻¹ * Bf g = 1 := by
  rw [← Bf_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

theorem Bf_mul_inv (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g * Bf g⁻¹ = 1 := by
  rw [← Bf_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

end Global

theorem pi_scale : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  intro F _ _ _ _ lf hH h1 ι _ _
  obtain ⟨hlc, hsc, ht2, hOc, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨hF, -, hU⟩ := GlobalTheory.T.adelic_haar_measure_scaling F lf hH h1
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  have hmeas : ∀ (g : Matrix ι ι F), g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s →
      MeasurableSet ((fun x => Bf g *ᵥ x) '' s) := by
    intro g hg s hs
    rw [image_mulVec_eq_preimage _ _ (Bf_mul_inv g hg) (Bf_inv_mul g hg)]
    exact (continuous_mulVec_left _).measurable hs
  refine ⟨?_, ?_⟩
  · intro g hg
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun g => ∀ s : Set (ι → A F), MeasurableSet s →
        (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) =
          ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) *
            (Measure.pi fun _ : ι => lf) s) g hg ?_ ?_ ?_
    · intro D hD s hs
      have hD' : ∀ i, D i ≠ 0 := by
        intro i
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      have hfun : (fun x : ι → A F => Bf (diagonal D) *ᵥ x) =
          fun x i => algebraMap F (A F) (D i) * x i := by
        funext x i
        have : Bf (diagonal D) = diagonal (fun i => algebraMap F (A F) (D i)) := by
          ext a b
          by_cases hab : a = b
          · subst hab; simp [Bf]
          · simp [Bf, hab]
        rw [this, mulVec_diagonal]
      rw [hfun, pi_image_mul lf (fun i => algebraMap F (A F) (D i))
        (fun i => algebraMap F (A F) (D i)⁻¹) ?_
        (fun i => Real.toNNReal (|((Algebra.norm ℚ (D i) : ℚ) : ℝ)|⁻¹)) ?_ s hs]
      · congr 1
        rw [det_diagonal, map_prod, Rat.cast_prod, Finset.abs_prod, ← Finset.prod_inv_distrib,
          ENNReal.ofReal_prod_of_nonneg fun i _ => inv_nonneg.2 (abs_nonneg _)]
        rfl
      · intro i
        rw [← map_mul, mul_inv_cancel₀ (hD' i), map_one]
      · intro i t ht
        exact hF (D i) (hD' i) t ht
    · intro t s hs
      have hdet : t.toMatrix.det = 1 := t.det
      have hinv : Bf t.toMatrix * Bf (transvection t.i t.j (-t.c)) = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hinv' : Bf (transvection t.i t.j (-t.c)) * Bf t.toMatrix = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hB : Bf (transvection t.i t.j (-t.c)) =
          transvection t.i t.j (algebraMap F (A F) (-t.c)) := by
        simp [Bf, transvection, Matrix.map_add, Matrix.map_one]
      rw [image_mulVec_eq_preimage _ _ hinv hinv', hB,
        (measurePreserving_transvection lf t.i t.j t.hij _).measure_preimage hs.nullMeasurableSet,
        hdet]
      simp
    · intro P Q hP hQ IP IQ s hs
      have himg : (fun x => Bf (P * Q) *ᵥ x) '' s =
          (fun x => Bf P *ᵥ x) '' ((fun x => Bf Q *ᵥ x) '' s) := by
        rw [Set.image_image]
        simp [Bf_mul, Matrix.mulVec_mulVec]
      rw [himg, IP _ (hmeas Q hQ s hs), IQ s hs, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _)),
        det_mul, map_mul, Rat.cast_mul, abs_mul, mul_inv]
  · intro a s hs
    have hfin : lf ((fun x => (a : A F) * x) '' Oh F) ≠ ∞ :=
      (hOc.image (continuous_const.mul continuous_id)).measure_lt_top.ne
    have hfun : (fun x : ι → A F => (a : A F) • x) = fun x i => (a : A F) * x i := by
      funext x i
      rfl
    rw [hfun, pi_image_mul lf (fun _ => (a : A F)) (fun _ => ((a⁻¹ : (A F)ˣ) : A F)) (fun _ => by simp)
      (fun _ => (lf ((fun x => (a : A F) * x) '' Oh F)).toNNReal) ?_ s hs]
    · simp [ENNReal.coe_toNNReal hfin]
    · intro _ t ht
      rw [ENNReal.coe_toNNReal hfin]
      exact hU a t ht

end GlobalTheory.CompanionTheory.SW.Core.PiScale
