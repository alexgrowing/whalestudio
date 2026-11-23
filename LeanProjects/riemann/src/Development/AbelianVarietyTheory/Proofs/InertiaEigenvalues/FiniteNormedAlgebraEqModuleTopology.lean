import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory

open MeasureTheory Filter Topology in

theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  haveI : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨⟨Units.isOpenEmbedding_val⟩, ?_⟩
  have hd := hasStrictFDerivAt_pow (𝕜 := F) 2 (x := (1 : R))
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hsurj : LinearMap.range
      ((((2 : ℕ) • (1 : R) ^ (2 - 1)) • ContinuousLinearMap.id F R : R →L[F] R) : R →ₗ[F] R)
        = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ⟨(2 : F)⁻¹ • v, ?_⟩
    have hc : ((2 : ℕ) • (1 : R) ^ (2 - 1)) = algebraMap F R 2 := by
      simp [two_smul, map_ofNat, one_add_one_eq_two]
    simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply,
      id_eq, hc, ContinuousLinearMap.coe_coe, smul_eq_mul]
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have hmap := hd.map_nhds_eq_of_surj hsurj
  rw [one_pow] at hmap
  rw [← hmap, Filter.eventually_map]
  exact Filter.Eventually.of_forall fun s => ⟨s, rfl⟩

open MeasureTheory Filter Topology in

theorem _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [N : NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R := by
  haveI : IsModuleTopology F R := isModuleTopologyOfFiniteDimensional
  exact eq_moduleTopology F R

open MeasureTheory Filter Topology in

theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  classical
  have h := eq_moduleTopology F R
  let b := Module.finBasis F R
  letI : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  letI N : NormedCommRing R :=
    NormedCommRing.induced R _ (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)
  letI : NormedAlgebra F R := NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed F R
  have h2 := _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology F R
  have h3 : τ = N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
    h.trans h2.symm
  rw [h3]
  exact key

end GlobalTheory
