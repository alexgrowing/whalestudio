import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereLawUnitary

def rowMap {N : ℕ} (k : ℕ) (U : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) :
    (Fin k × Fin N → ℂ) →ₗ[ℝ] (Fin k × Fin N → ℂ) where
  toFun u ij := U (fun j ↦ u (ij.1, j)) ij.2
  map_add' u v := by
    funext ij
    have : (fun j ↦ (u + v) (ij.1, j)) = (fun j ↦ u (ij.1, j)) + fun j ↦ v (ij.1, j) := rfl
    change U (fun j ↦ (u + v) (ij.1, j)) ij.2 =
      U (fun j ↦ u (ij.1, j)) ij.2 + U (fun j ↦ v (ij.1, j)) ij.2
    rw [this, map_add]
    rfl
  map_smul' r u := by
    funext ij
    have : (fun j ↦ (r • u) (ij.1, j)) = (r : ℂ) • fun j ↦ u (ij.1, j) := by
      funext j; simp [Complex.real_smul]
    change U (fun j ↦ (r • u) (ij.1, j)) ij.2 = r • U (fun j ↦ u (ij.1, j)) ij.2
    rw [this, map_smul]
    simp [Complex.real_smul]

theorem proof : SphereLawUnitary.Statement := by
  intro N U hU
  set B := sphereBall (HermNorm.std N) 1 with hBdef
  set g : (Fin 1 × Fin N → ℂ) → (Fin N → ℂ) :=
    fun u j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j) with hgdef
  set V := rowMap 1 U with hVdef
  have hrow : ∀ u i, (fun j ↦ V u (i, j)) = U (fun j ↦ u (i, j)) := fun _ _ ↦ rfl
  have hnorm : ∀ v, (HermNorm.std N).norm (U v) = (HermNorm.std N).norm v := by
    intro v; simp only [HermNorm.std_norm_eq, hU]
  have hBm : MeasurableSet B := (isOpen_sphereBall_std N).measurableSet
  have hVm : Measurable V := V.continuous_of_finiteDimensional.measurable
  have hUm : Measurable U := U.continuous_of_finiteDimensional.measurable
  have hgm : Measurable g := by
    simp only [hgdef, sphereNormalize, HermNorm.std_norm_eq]
    fun_prop
  have hpre : V ⁻¹' B = B := by
    ext u
    simp only [Set.mem_preimage, hBdef, sphereBall, Set.mem_ofPred_eq, hrow, hnorm]
  have hcomm : U ∘ g = g ∘ V := by
    funext u
    have hg : ∀ w, g w = (((HermNorm.std N).norm fun j ↦ w (0, j) : ℝ) : ℂ)⁻¹ •
        fun j ↦ w (0, j) := fun w ↦ by
      funext j; simp [hgdef, sphereNormalize]
    simp only [Function.comp_apply, hg, map_smul, hrow, hnorm]
  have hinj : Function.Injective V := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext ij
    have h1 : U (fun j ↦ u (ij.1, j)) = 0 := by rw [← hrow, hu]; rfl
    have h2 := hU (fun j ↦ u (ij.1, j))
    rw [h1] at h2
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h2
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)).mp h2.symm ij.2
      (Finset.mem_univ _)
    simpa using this
  have hdet : LinearMap.det V ≠ 0 := by
    have h := (LinearEquiv.ofInjectiveEndo V hinj).isUnit_det'
    have e : ((LinearEquiv.ofInjectiveEndo V hinj : _ ≃ₗ[ℝ] _) : _ →ₗ[ℝ] _) = V :=
      LinearMap.ext fun x ↦ by simp [LinearEquiv.coe_ofInjectiveEndo]
    rw [e] at h
    exact h.ne_zero
  have h0 : volume B ≠ 0 := by
    refine ((isOpen_sphereBall_std N).measure_pos volume ⟨0, ?_⟩).ne'
    simp [sphereBall, HermNorm.std_norm_eq]
  have htop : volume B ≠ ⊤ :=
    ((measure_mono (sphereBall_std_subset N)).trans_lt
      (isCompact_closedBall 0 1).measure_lt_top).ne
  have hvol : Measure.map V volume = (volume : Measure (Fin 1 × Fin N → ℂ)) := by
    have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (Fin 1 × Fin N → ℂ)) hdet
    have hc : ENNReal.ofReal |(LinearMap.det V)⁻¹| = 1 := by
      have hB := congrArg (fun μ : Measure (Fin 1 × Fin N → ℂ) ↦ μ B) hmap
      simp only [Measure.map_apply hVm hBm, hpre, Measure.smul_apply, smul_eq_mul] at hB
      have : 1 * volume B = ENNReal.ofReal |(LinearMap.det V)⁻¹| * volume B := by
        rw [one_mul]; exact hB
      exact ((ENNReal.mul_left_inj h0 htop).mp this).symm
    rw [hmap, hc, one_smul]
  have hcond : Measure.map V (volume[|B]) = volume[|B] := by
    rw [ProbabilityTheory.cond, Measure.map_smul, ← hpre, ← Measure.restrict_map hVm hBm,
      hvol, hpre]
  show Measure.map U (Measure.map g (volume[|B])) = Measure.map g (volume[|B])
  rw [Measure.map_map hUm hgm, hcomm, ← Measure.map_map hgm hVm, hcond]

end SphereLawUnitary

end

end GroundTheory.Heights₂.Heights
