import Mathlib
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding
  IsDedekindDomain MeasureTheory Measure Matrix Module TensorProduct
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical nonZeroDivisors

noncomputable section

set_option synthInstance.maxSize 1000
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]

variable (K X) in

abbrev AdelicPoints : Type _ := 𝔸[K] ⊗[K] X

instance : TopologicalSpace (AdelicPoints K X) := moduleTopology 𝔸[K] (AdelicPoints K X)

instance : IsModuleTopology 𝔸[K] (AdelicPoints K X) := ⟨rfl⟩

instance : ContinuousAdd (AdelicPoints K X) := IsModuleTopology.toContinuousAdd 𝔸[K] _

instance : IsTopologicalAddGroup (AdelicPoints K X) := IsModuleTopology.topologicalAddGroup 𝔸[K] _

instance : MeasurableSpace (AdelicPoints K X) := borel _

instance : BorelSpace (AdelicPoints K X) := ⟨rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

def adelicCoord (b : Basis ι K X) : AdelicPoints K X ≃ₗ[𝔸[K]] (ι → 𝔸[K]) :=
  (b.baseChange 𝔸[K]).equivFun

theorem adelicCoord_tmul (b : Basis ι K X) (a : 𝔸[K]) (x : X) :
    adelicCoord b (a ⊗ₜ x) = fun i ↦ algebraMap K 𝔸[K] (b.repr x i) * a := by
  funext i
  rw [adelicCoord, Basis.equivFun_apply, Basis.baseChange_repr_tmul, Algebra.smul_def]

theorem adelicCoord_symm_apply (b : Basis ι K X) (x : ι → 𝔸[K]) :
    (adelicCoord b).symm x = ∑ i, x i • ((1 : 𝔸[K]) ⊗ₜ[K] b i) := by
  rw [adelicCoord, Basis.equivFun_symm_apply]
  simp only [Basis.baseChange_apply]

def adelicCoordHomeomorph (b : Basis ι K X) : AdelicPoints K X ≃ₜ (ι → 𝔸[K]) where
  toEquiv := (adelicCoord b).toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (adelicCoord b).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (adelicCoord b).symm.toLinearMap

theorem measurableEmbedding_adelicCoord_symm (b : Basis ι K X) :
    MeasurableEmbedding (adelicCoord b).symm :=
  (adelicCoordHomeomorph b).symm.measurableEmbedding

theorem measurable_adelicCoord_symm (b : Basis ι K X) : Measurable (adelicCoord b).symm :=
  (measurableEmbedding_adelicCoord_symm b).measurable

theorem adelicCoord_adelicCoord_symm (b : Basis ι K X) (c : Basis κ K X) (x : ι → 𝔸[K]) :
    adelicCoord c ((adelicCoord b).symm x) = (c.toMatrix b).map (algebraMap K 𝔸[K]) *ᵥ x := by
  rw [adelicCoord_symm_apply, _root_.map_sum]
  funext k
  simp only [map_smul, adelicCoord_tmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_one,
    Matrix.mulVec, dotProduct, Matrix.map_apply, Basis.toMatrix_apply]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

variable (K X) in

def adelicPointsMeasure : Measure (AdelicPoints K X) :=
  (adeleMeasurePi K (ι := Fin (finrank K X))).map (adelicCoord (Module.finBasis K X)).symm

theorem adelicPointsMeasure_eq_map (b : Basis ι K X) :
    adelicPointsMeasure K X = (adeleMeasurePi K).map (adelicCoord b).symm := by
  set c := Module.finBasis K X
  have hfun : ⇑(adelicCoord b).symm =
      (adelicCoord c).symm ∘ fun x ↦ (c.toMatrix b).map (algebraMap K 𝔸[K]) *ᵥ x := by
    funext x
    simp only [Function.comp_apply]
    rw [← adelicCoord_adelicCoord_symm b c x, LinearEquiv.symm_apply_apply]
  have hmp := measurePreserving_mulVec (c.toMatrix b) (b.toMatrix c)
    (Basis.toMatrix_mul_toMatrix_flip b c) (Basis.toMatrix_mul_toMatrix_flip c b)
  rw [hfun, ← Measure.map_map (measurable_adelicCoord_symm c) hmp.measurable, hmp.map_eq]
  rfl

instance : (adelicPointsMeasure K X).IsAddHaarMeasure :=
  isAddHaarMeasure_map _ (adelicCoord (Module.finBasis K X)).symm.toLinearMap.toAddMonoidHom
    (adelicCoordHomeomorph (Module.finBasis K X)).symm.continuous
    (adelicCoord (Module.finBasis K X)).symm.surjective
    (adelicCoordHomeomorph (Module.finBasis K X)).symm.isClosedEmbedding.tendsto_cocompact

variable (K X) in

def schwartzBruhatPoints : Submodule ℂ (AdelicPoints K X → ℂ) :=
  (schwartzBruhatPi K (Fin (finrank K X))).comap
    (LinearMap.funLeft ℂ ℂ (adelicCoord (Module.finBasis K X)).symm)

theorem mem_schwartzBruhatPoints_iff (b : Basis ι K X) {f : AdelicPoints K X → ℂ} :
    f ∈ schwartzBruhatPoints K X ↔ f ∘ (adelicCoord b).symm ∈ schwartzBruhatPi K ι := by
  set c := Module.finBasis K X
  change f ∘ (adelicCoord c).symm ∈ schwartzBruhatPi K (Fin (finrank K X)) ↔ _
  constructor
  · intro h
    have h' := comp_mulVec_mem_schwartzBruhatPi (c.toMatrix b) (b.toMatrix c)
      (Basis.toMatrix_mul_toMatrix_flip b c) (Basis.toMatrix_mul_toMatrix_flip c b) h
    convert h' using 1
    funext x
    simp only [Function.comp_apply]
    rw [← adelicCoord_adelicCoord_symm b c x, LinearEquiv.symm_apply_apply]
  · intro h
    have h' := comp_mulVec_mem_schwartzBruhatPi (b.toMatrix c) (c.toMatrix b)
      (Basis.toMatrix_mul_toMatrix_flip c b) (Basis.toMatrix_mul_toMatrix_flip b c) h
    convert h' using 1
    funext x
    simp only [Function.comp_apply]
    rw [← adelicCoord_adelicCoord_symm c b x, LinearEquiv.symm_apply_apply]

variable (B : LinearMap.BilinForm K X)

abbrev adelicForm : LinearMap.BilinForm 𝔸[K] (AdelicPoints K X) := B.baseChange 𝔸[K]

def pointsFourier (f : AdelicPoints K X → ℂ) (y : AdelicPoints K X) : ℂ :=
  ∫ x, f x * (adelicChar K (adelicForm B x y) : ℂ) ∂adelicPointsMeasure K X

def rationalAdelicPoint : X →ₗ[K] AdelicPoints K X := TensorProduct.mk K 𝔸[K] X 1

variable (K) in

def lineForm : LinearMap.BilinForm K K := LinearMap.mul K K

variable (K ι) in

def gaussianInfPi : 𝓢(ι → mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K (ι := ι)) (gaussianSchwartz (EuclidPi K ι))

variable (K) in

def gaussianLattice : AdelicPoints K K → ℂ :=
  schwartzBruhatTensorPi (gaussianInfPi K (Fin (finrank K K)))
      (finiteTensor fun _ ↦ cosetIndicator (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) 0) ∘
    adelicCoord (Module.finBasis K K)

end

end GroundTheory.Heights₂.Theta
