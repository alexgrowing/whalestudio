import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric
open scoped Pointwise

private theorem toSphere_univ_ne_zero_of_pos {n : ℕ} (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
  have : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    ⟨⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ), 0, fun h => by
        simpa using congrArg norm h⟩⟩
  rw [Measure.toSphere_apply_univ]
  refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
  exact_mod_cast (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℂ (Fin n))).ne'

private theorem toSphere_univ_ne_top' {n : ℕ} :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
  exact measure_ne_top _ _

theorem isProbabilityMeasure_sphereProb {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (sphereProb n) := by
  constructor
  simp only [sphereProb, ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (toSphere_univ_ne_zero_of_pos hn) toSphere_univ_ne_top'

private theorem volume_preimage_linearIsometryEquiv {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (X : Set (EuclideanSpace ℂ (Fin n))) : volume (A ⁻¹' X) = volume X :=
  A.measurePreserving.measure_preimage_emb A.toHomeomorph.measurableEmbedding X

private theorem Ioo_smul_image_preimage_sphere_eq_preimage {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) (s : Set (UnitSphereC n)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((fun z : UnitSphereC n =>
        (⟨A z, by simp⟩ : UnitSphereC n)) ⁻¹' s)) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨r, hr, _, ⟨⟨A z, by simp⟩, hz, rfl⟩, ?_⟩
    exact (map_smul A r (z : EuclideanSpace ℂ (Fin n))).symm
  · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨A.symm w, by simp⟩, ?_, rfl⟩, ?_⟩
    · have hw' : (⟨A (A.symm (w : EuclideanSpace ℂ (Fin n))), by simp⟩ : UnitSphereC n) = w :=
        Subtype.ext (by simp)
      exact (congrArg (· ∈ s) hw').mpr hw
    · show r • A.symm (w : EuclideanSpace ℂ (Fin n)) = x
      calc r • A.symm (w : EuclideanSpace ℂ (Fin n))
          = A.symm (r • (w : EuclideanSpace ℂ (Fin n))) :=
            (map_smul A.symm r (w : EuclideanSpace ℂ (Fin n))).symm
        _ = x := by rw [hx, LinearIsometryEquiv.symm_apply_apply]

theorem measurePreserving_toSphere_isometry {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n))
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hcont : Continuous (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n)) :=
    (A.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨hcont.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hcont.measurable hs, Measure.toSphere_apply' (μ := volume) (hcont.measurable hs),
    Measure.toSphere_apply' (μ := volume) hs, Ioo_smul_image_preimage_sphere_eq_preimage A s,
    volume_preimage_linearIsometryEquiv]

def rotLIE {n : ℕ} (u : Fin n → Circle) : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j => rotation (u j)

theorem rotLIE_apply {n : ℕ} (u : Fin n → Circle) (x : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (rotLIE u x).ofLp j = (u j : ℂ) * x.ofLp j := by
  rfl

def sphereRot {n : ℕ} (u : Fin n → Circle) (z : UnitSphereC n) : UnitSphereC n :=
  ⟨rotLIE u z, by simp⟩

private theorem measurePreserving_sphereProb_of_toSphere {n : ℕ} {f : UnitSphereC n → UnitSphereC n}
    (hf : MeasurePreserving f (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere) :
    MeasurePreserving f (sphereProb n) (sphereProb n) := by
  refine ⟨hf.measurable, ?_⟩
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ]
  rw [Measure.map_smul, hf.map_eq]

theorem measurePreserving_sphereRot {n : ℕ} (u : Fin n → Circle) :
    MeasurePreserving (sphereRot u) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereProb_of_toSphere (f := sphereRot u)
    (measurePreserving_toSphere_isometry (rotLIE u))

def blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) : BlockSphere B n :=
  fun b => sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b)

private theorem coe_circle_exp_two_pi_mul (t : ℝ) :
    ((Circle.exp (2 * Real.pi * t) : Circle) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem blockPoint_blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) :
    blockPoint (blockRot θ z) = fun p => blockPoint z p * torusPoint θ p := by
  funext p
  obtain ⟨b, j⟩ := p
  show WithLp.ofLp (rotLIE (fun j' => Circle.exp (2 * Real.pi * θ (b, j')))
      (z b : EuclideanSpace ℂ (Fin n))) j =
    WithLp.ofLp (z b : EuclideanSpace ℂ (Fin n)) j * torusPoint θ (b, j)
  rw [rotLIE_apply]
  simp only [coe_circle_exp_two_pi_mul, torusPoint]
  ring

theorem measurePreserving_blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) :
    MeasurePreserving (blockRot θ) (blockSphereProb B n) (blockSphereProb B n) := by
  have h : ∀ b : Fin B, MeasurePreserving
      (sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))))
      (sphereProb n) (sphereProb n) := fun b => measurePreserving_sphereRot _
  show MeasurePreserving (fun (z : BlockSphere B n) (b : Fin B) =>
      sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b))
    (Measure.pi fun _ => sphereProb n) (Measure.pi fun _ => sphereProb n)
  exact measurePreserving_pi (hf := h)

theorem sphereProb_coord_zero {n : ℕ} (j : Fin n) :
    sphereProb n {z | spherePoint z j = 0} = 0 := by
  let W : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ).toLinearMap
  have hW : W ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ W := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at hmem
    change WithLp.ofLp (EuclideanSpace.single j (1 : ℂ)) j = 0 at hmem
    simp at hmem
  have hW0 : (volume : Measure (EuclideanSpace ℂ (Fin n))) (W : Set (EuclideanSpace ℂ (Fin n))) = 0 :=
    Measure.addHaar_submodule _ W hW
  have hmeas : MeasurableSet {z : UnitSphereC n | spherePoint z j = 0} := by
    have hc : Continuous fun z : UnitSphereC n => spherePoint z j := by
      exact (continuous_apply j).comp ((EuclideanSpace.equiv (Fin n) ℂ).continuous.comp
        continuous_subtype_val)
    exact (isClosed_singleton.preimage hc).measurableSet
  have hS : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | spherePoint z j = 0} = 0 := by
    rw [Measure.toSphere_apply' (μ := volume) hmeas]
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ hW0)
    rintro x ⟨r, -, _, ⟨z, hz, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, spherePoint] at hz
    show ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ)
      (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    show r • WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) j = 0
    rw [hz, smul_zero]
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, hS, mul_zero]

theorem blockSphereProb_coord_zero {B n : ℕ} :
    blockSphereProb B n {z | ∃ p : Fin B × Fin n, blockPoint z p = 0} = 0 := by
  rw [Set.ofPred_exists]
  refine measure_iUnion_null fun p => ?_
  show (Measure.pi fun _ : Fin B => sphereProb n)
    (Function.eval p.1 ⁻¹' {w : UnitSphereC n | spherePoint w p.2 = 0}) = 0
  exact Measure.pi_eval_preimage_null _ (sphereProb_coord_zero p.2)

theorem norm_blockPoint_le {B n : ℕ} (z : BlockSphere B n) (p : Fin B × Fin n) :
    ‖blockPoint z p‖ ≤ 1 := by
  have h1 : ‖((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
  have h2 := EuclideanSpace.norm_eq ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))
  rw [h1] at h2
  have h3 : ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) p.2‖ ^ 2 ≤
      ∑ i, ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖WithLp.ofLp ((z p.1 : UnitSphereC n) :
      EuclideanSpace ℂ (Fin n)) i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ _)
  have h4 := Real.sqrt_le_sqrt h3
  rw [← h2, Real.sqrt_sq (norm_nonneg _)] at h4
  exact h4

end ReciprocityTheory.MultiplicativeHeights
