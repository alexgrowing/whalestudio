import Mathlib
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

set_option maxSynthPendingDepth 1

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain MeasureTheory Measure Matrix GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic.GJMatrix
open scoped NumberField.AdeleRing ENNReal NNReal

noncomputable section

namespace EllipticTorus

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in

def adeleCoordEquiv : 𝔸[L] ≃ₗ[𝔸[K]] (Fin (Module.finrank K L) → 𝔸[K]) :=
  (adeleBasis (Module.finBasis K L)).equivFun

theorem continuous_adeleCoordEquiv : Continuous (adeleCoordEquiv K L) := by
  have := isModuleTopology_adeleRing (K := K) (L := L)
  exact IsModuleTopology.continuous_of_linearMap (adeleCoordEquiv K L).toLinearMap

theorem continuous_adeleCoordEquiv_symm : Continuous (adeleCoordEquiv K L).symm := by
  have := isModuleTopology_adeleRing (K := K) (L := L)
  exact IsModuleTopology.continuous_of_linearMap (adeleCoordEquiv K L).symm.toLinearMap

variable (K L) in

def adeleCoordHomeomorph : 𝔸[L] ≃ₜ (Fin (Module.finrank K L) → 𝔸[K]) where
  toEquiv := (adeleCoordEquiv K L).toEquiv
  continuous_toFun := continuous_adeleCoordEquiv
  continuous_invFun := continuous_adeleCoordEquiv_symm

def mulMatrixGL (x : (𝔸[L])ˣ) : GL (Fin (Module.finrank K L)) 𝔸[K] where
  val := (Algebra.leftMulMatrix (adeleBasis (Module.finBasis K L)) (x : 𝔸[L]))ᵀ
  inv := (Algebra.leftMulMatrix (adeleBasis (Module.finBasis K L)) ((x⁻¹ : (𝔸[L])ˣ) : 𝔸[L]))ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← map_mul, Units.inv_mul, map_one, Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← map_mul, Units.mul_inv, map_one, Matrix.transpose_one]

theorem det_mulMatrixGL (x : (𝔸[L])ˣ) :
    ((Matrix.GeneralLinearGroup.det (mulMatrixGL (K := K) x) : (𝔸[K])ˣ) : 𝔸[K]) =
      Algebra.norm 𝔸[K] (x : 𝔸[L]) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Algebra.norm_eq_matrix_det
    (adeleBasis (Module.finBasis K L))]
  exact Matrix.det_transpose _

theorem adeleCoordEquiv_mul (x : (𝔸[L])ˣ) (y : 𝔸[L]) :
    adeleCoordEquiv K L ((x : 𝔸[L]) * y) =
      adeleCoordEquiv K L y ᵥ* (mulMatrixGL (K := K) x : Matrix _ _ 𝔸[K]) := by
  change _ = _ ᵥ* (Algebra.leftMulMatrix (adeleBasis (Module.finBasis K L)) (x : 𝔸[L]))ᵀ
  rw [Matrix.vecMul_transpose, adeleCoordEquiv, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    Algebra.leftMulMatrix_mulVec_repr]

variable (K L) in

def coordMeasure : Measure 𝔸[L] :=
  (adeleMeasurePi K (ι := Fin (Module.finrank K L))).map (adeleCoordEquiv K L).symm

theorem measurable_adeleCoordEquiv_symm : Measurable (adeleCoordEquiv K L).symm :=
  continuous_adeleCoordEquiv_symm.measurable

instance isAddHaarMeasure_coordMeasure : (coordMeasure K L).IsAddHaarMeasure :=
  isAddHaarMeasure_map _ (adeleCoordEquiv K L).symm.toLinearMap.toAddMonoidHom
    continuous_adeleCoordEquiv_symm (adeleCoordEquiv K L).symm.surjective
    (adeleCoordHomeomorph K L).symm.isClosedEmbedding.tendsto_cocompact

theorem map_smul_coordMeasure (x : IdeleGroup L) :
    (coordMeasure K L).map (fun y ↦ x • y) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K (ideleNorm K L x) : ℝ))⁻¹ • coordMeasure K L := by
  have hdet : Matrix.GeneralLinearGroup.det (mulMatrixGL (K := K) x) = ideleNorm K L x :=
    Units.ext (det_mulMatrixGL x)
  have hcomp : (fun y : 𝔸[L] ↦ x • y) ∘ (adeleCoordEquiv K L).symm =
      (adeleCoordEquiv K L).symm ∘
        (fun v ↦ v ᵥ* (mulMatrixGL (K := K) x : Matrix _ _ 𝔸[K])) := by
    funext v
    apply (adeleCoordEquiv K L).injective
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
    rw [Units.smul_def, smul_eq_mul, adeleCoordEquiv_mul, LinearEquiv.apply_symm_apply]
  rw [coordMeasure, Measure.map_map (continuous_const_smul x).measurable
      measurable_adeleCoordEquiv_symm, hcomp,
    ← Measure.map_map measurable_adeleCoordEquiv_symm
      (GJGlobal.Modulus.measurable_vecMul' (mulMatrixGL (K := K) x)),
    GJGlobal.Modulus.map_vecMul_adeleMeasurePi, Measure.map_smul, hdet]

theorem ideleModule_ideleNorm (x : IdeleGroup L) :
    IdeleGroup.ideleModule K (ideleNorm K L x) = IdeleGroup.ideleModule L x := by
  have hc := isAddLeftInvariant_eq_smul (coordMeasure K L) (adeleMeasure L)
  set c := (coordMeasure K L).addHaarScalarFactor (adeleMeasure L)
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    have : coordMeasure K L = 0 := by rw [hc, ENNReal.coe_eq_zero.1 h, zero_smul]
    exact (NeZero.ne (coordMeasure K L)) this
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : 𝔸[L])
  have hpos : adeleMeasure L S ≠ 0 := (measure_pos_of_mem_nhds _ hS0).ne'
  have htop : adeleMeasure L S ≠ ⊤ := hS.measure_lt_top.ne
  have h1 := map_smul_coordMeasure (K := K) x
  rw [hc, Measure.map_smul, map_smul_adeleMeasure] at h1
  have h2 := congrArg (fun μ : Measure 𝔸[L] ↦ μ S) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  rw [mul_left_comm] at h2
  have hne : (c : ℝ≥0∞) * adeleMeasure L S ≠ 0 := mul_ne_zero hc0 hpos
  have hnt : (c : ℝ≥0∞) * adeleMeasure L S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top htop
  have h3 := (ENNReal.mul_left_inj hne hnt).1 h2
  have h4 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule L x).2.le)
    (inv_nonneg.2 (IdeleGroup.ideleModule K (ideleNorm K L x)).2.le)).1 h3
  exact Subtype.ext (inv_inj.1 h4).symm

end EllipticTorus

end

end GroundTheory.Automorphic
