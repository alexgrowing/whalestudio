import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiscreteHaar

noncomputable section

open MeasureTheory Set Function Topology
open scoped ENNReal NNReal Pointwise

namespace PI.NglqJacSplitW

section Diag

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def scaleAt (i : ι) (a : F) (ha : a ≠ 0) : (ι → F) ≃ₜ+ (ι → F) where
  toFun x := update x i (a * x i)
  invFun x := update x i (a⁻¹ * x i)
  left_inv x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [inv_mul_cancel_left₀ ha]
    · simp [update_of_ne hj]
  right_inv x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [mul_inv_cancel_left₀ ha]
    · simp [update_of_ne hj]
  map_add' x y := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [mul_add]
    · simp [update_of_ne hj]
  continuous_toFun := continuous_id.update i (continuous_const.mul (continuous_apply i))
  continuous_invFun := continuous_id.update i (continuous_const.mul (continuous_apply i))

theorem image_update_pi (i : ι) (a : F) (_ha : a ≠ 0) (s : ι → Set F) :
    (fun x => update x i (a * x i)) '' (univ.pi s) =
      univ.pi (update s i ((fun y => a * y) '' s i)) := by
  ext y
  simp only [Set.mem_image, Set.mem_univ_pi]
  constructor
  · rintro ⟨x, hx, rfl⟩ j
    by_cases hj : j = i
    · subst hj
      simp only [update_self]
      exact ⟨x j, hx j, rfl⟩
    · simp only [update_of_ne hj]
      exact hx j
  · intro hy
    have hyi := hy i
    simp only [update_self, Set.mem_image] at hyi
    obtain ⟨t, ht, hti⟩ := hyi
    refine ⟨update y i t, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        simpa using ht
      · have := hy j
        simpa [update_of_ne hj] using this
    · funext j
      by_cases hj : j = i
      · subst hj
        simp [hti]
      · simp [update_of_ne hj]

end Diag

theorem diagonal_one_jacobian : DiagOne := by
  intro F _ _ _ _ _ _ ι _ _ mι bι i a ha ν hν S hS
  have hpi : mι = @MeasurableSpace.pi ι (fun _ => F) (fun _ => borel F) := by
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    rw [bι.measurable_eq]
    exact (Pi.borelSpace (ι := ι) (X := fun _ => F)).measurable_eq.symm
  subst hpi
  letI mF : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := hν
  set μ : Measure F := Measure.addHaar with hμ
  set P : Measure (ι → F) := Measure.pi fun _ => μ with hP
  set m' : ℝ≥0 := distribHaarChar F (Units.mk0 a ha) with hm'
  have hmod : modF F a = (m' : ℝ≥0∞) := by simp [modF, ha, hm']
  set φ := scaleAt i a ha with hφ
  have himg : ∀ T : Set (ι → F), φ '' T = φ.symm ⁻¹' T := fun T => by
    rw [Set.image_eq_preimage_of_inverse (fun x => φ.symm_apply_apply x)
      (fun x => φ.apply_symm_apply x)]
  have hφm : Measurable φ.symm := φ.symm.continuous.measurable
  have hscal : ∀ t : Set F, μ ((fun y => a * y) '' t) = m' * μ t := fun t => by
    rw [distribHaarChar_mul μ (Units.mk0 a ha) t, ← Set.image_smul]
    rfl
  set μs : ι → Measure F := update (fun _ => μ) i (m' • μ) with hμs
  have hsf : ∀ j, SigmaFinite (μs j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [hμs, update_self]
      infer_instance
    · simp only [hμs, update_of_ne hj]
      infer_instance
  have hA : Measure.pi μs = Measure.map φ.symm P := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hφm (MeasurableSet.univ_pi hs), ← himg]
    rw [show ((φ : (ι → F) → (ι → F)) '' univ.pi s) =
        (fun x => update x i (a * x i)) '' univ.pi s from rfl, image_update_pi i a ha s, hP,
      Measure.pi_pi]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp only [hμs, update_self, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hscal]
    · simp only [hμs, update_of_ne hj]
  have hB : Measure.pi μs = m' • P := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, hP, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
      ← Finset.mul_prod_erase Finset.univ (fun j => μs j (s j)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => μ (s j)) (Finset.mem_univ i)]
    have herase : ∏ j ∈ Finset.univ.erase i, μs j (s j) = ∏ j ∈ Finset.univ.erase i, μ (s j) :=
      Finset.prod_congr rfl fun j hj => by
        simp only [hμs, update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [herase]
    simp only [hμs, update_self, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    ring
  have hmap : Measure.map φ.symm P = m' • P := hA.symm.trans hB
  have hPS : P (φ '' S) = m' * P S := by
    rw [himg, ← Measure.map_apply hφm hS, hmap, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
  have hνP : ν = ν.addHaarScalarFactor P • P := Measure.isAddLeftInvariant_eq_smul ν P
  show ν (φ '' S) = modF F a * ν S
  rw [hmod, hνP, Measure.smul_apply, Measure.smul_apply, hPS, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul]
  ring

end PI.NglqJacSplitW
