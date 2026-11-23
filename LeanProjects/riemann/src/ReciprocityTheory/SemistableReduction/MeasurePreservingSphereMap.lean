import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric
open scoped Pointwise

def sphereMap {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (z : UnitSphereC n) : UnitSphereC n :=
  ⟨U z, by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
           exact mem_sphere_zero_iff_norm.mp z.2⟩

theorem continuous_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Continuous (sphereMap U) :=
  (U.continuous.comp continuous_subtype_val).subtype_mk _

theorem toSphere_map_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Measure.map (sphereMap U) (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere =
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hmeas := (continuous_sphereMap U).measurable
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.toSphere_apply' _ (hmeas hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hset : (Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap U ⁻¹' s) :
      Set (EuclideanSpace ℂ (Fin n)))) = U ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, U z, ⟨sphereMap U z, hz, rfl⟩, (map_smul U r (z : EuclideanSpace ℂ (Fin n))).symm⟩
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hxy⟩
      refine ⟨r, hr, U.symm z, ⟨sphereMap U.symm z, ?_, rfl⟩, ?_⟩
      · have : sphereMap U (sphereMap U.symm z) = z := Subtype.ext (by simp [sphereMap])
        rw [this]; exact hz
      · rw [← map_smul, hxy]; simp
  rw [hset]
  have hU : MeasurePreserving (U.toHomeomorph.toMeasurableEquiv) volume volume :=
    U.measurePreserving
  exact hU.measure_preimage_equiv _

theorem measurePreserving_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (sphereMap U) (sphereProb n) (sphereProb n) := by
  refine ⟨(continuous_sphereMap U).measurable, ?_⟩
  unfold sphereProb ProbabilityTheory.cond
  rw [Measure.restrict_univ, Measure.map_smul, toSphere_map_sphereMap]

def rotCL {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (innerSL ℂ u).smulRight u + t • (ContinuousLinearMap.id ℂ _ - (innerSL ℂ u).smulRight u)

theorem rotCL_apply {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    rotCL u t x = inner ℂ u x • u + t • (x - inner ℂ u x • u) := by
  simp [rotCL]

theorem norm_rotCL {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1)
    (x : EuclideanSpace ℂ (Fin n)) : ‖rotCL u t x‖ = ‖x‖ := by
  have huu : inner ℂ u u = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have horth : inner ℂ u (x - inner ℂ u x • u) = 0 := by
    rw [inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
  have h1 : inner ℂ (inner ℂ u x • u) (t • (x - inner ℂ u x • u)) = 0 := by
    rw [inner_smul_left, inner_smul_right, horth]; simp
  have h2 : inner ℂ (inner ℂ u x • u) (x - inner ℂ u x • u) = 0 := by
    rw [inner_smul_left, horth]; simp
  have hx : x = inner ℂ u x • u + (x - inner ℂ u x • u) := by abel
  have key : ‖rotCL u t x‖ * ‖rotCL u t x‖ = ‖x‖ * ‖x‖ := by
    rw [rotCL_apply, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1,
      norm_smul t (x - inner ℂ u x • u), ht, one_mul]
    conv_rhs => rw [hx, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp key

def rotIso {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := ((rotCL u t : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)
      norm_map' := norm_rotCL hu ht } rfl

def rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    UnitSphereC n → UnitSphereC n :=
  sphereMap (rotIso hu (t := circleMap 0 1 θ) (by simp [norm_circleMap_zero]))

theorem coe_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ)
    (z : UnitSphereC n) :
    (rotS hu θ z : EuclideanSpace ℂ (Fin n)) =
      inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u +
        circleMap 0 1 θ • ((z : EuclideanSpace ℂ (Fin n)) - inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u) :=
  rotCL_apply u _ _

theorem measurePreserving_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    MeasurePreserving (rotS hu θ) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereMap _

theorem continuous_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    Continuous (fun p : ℝ × UnitSphereC n => rotS hu p.1 p.2) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_rotS]
  have hc : Continuous fun p : ℝ × UnitSphereC n => (p.2 : EuclideanSpace ℂ (Fin n)) :=
    continuous_subtype_val.comp continuous_snd
  have hθ : Continuous fun p : ℝ × UnitSphereC n => circleMap 0 1 p.1 :=
    (continuous_circleMap 0 1).comp continuous_fst
  have hi : Continuous fun p : ℝ × UnitSphereC n => inner ℂ u (p.2 : EuclideanSpace ℂ (Fin n)) :=
    continuous_const.inner hc
  exact (hi.smul continuous_const).add (hθ.smul (hc.sub (hi.smul continuous_const)))

theorem sphereProb_inner_eq_zero {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : u ≠ 0) :
    sphereProb n {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0} = 0 := by
  set s : Set (UnitSphereC n) := {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0}
  have hs : MeasurableSet s :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  let P : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ)
  have hP : P ≠ ⊤ := by
    intro h
    have hmem : u ∈ P := h ▸ Submodule.mem_top
    simp only [P, LinearMap.mem_ker, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply] at hmem
    exact hu (inner_self_eq_zero.mp hmem)
  have hsub : Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set (EuclideanSpace ℂ (Fin n))) ⊆ (P : Set (EuclideanSpace ℂ (Fin n))) := by
    rintro _ ⟨r, -, y, ⟨z, hz, rfl⟩, rfl⟩
    show (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ) (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    simp only [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [show inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0 from hz, smul_zero]
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere s = 0 := by
    rw [Measure.toSphere_apply' _ hs]
    rw [measure_mono_null hsub (Measure.addHaar_submodule _ P hP), mul_zero]
  simp [sphereProb, ProbabilityTheory.cond, h0]

end ReciprocityTheory.MultiplicativeHeights
