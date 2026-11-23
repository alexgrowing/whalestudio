import Mathlib
import GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

namespace AdeleBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def tmulLeft (l : L) : 𝔸[K] →ₗ[𝔸[K]] L ⊗[K] 𝔸[K] where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem adeleTensorEquiv_one_tmul_mul (a : 𝔸[K]) (t : L ⊗[K] 𝔸[K]) :
    adeleTensorEquiv K L ((1 ⊗ₜ a) * t) = adeleMap K L a * adeleTensorEquiv K L t := by
  rw [map_mul, adeleTensorEquiv_tmul, map_one, one_mul]

variable (K L) in

def adeleTensorSemilinear : L ⊗[K] 𝔸[K] →ₛₗ[adeleMap K L] 𝔸[L] where
  toFun := adeleTensorEquiv K L
  map_add' := map_add _
  map_smul' c t := adeleTensorEquiv_one_tmul_mul c t

variable (K L) in

def adeleTensorHomeomorph :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃ₜ 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  haveI : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd 𝔸[K] (L ⊗[K] 𝔸[K])
  { toEquiv := (adeleTensorEquiv K L).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMapₛₗ continuous_adeleMap (adeleTensorSemilinear K L)
    continuous_invFun := by
      have h : ∀ y, (adeleTensorEquiv K L).symm y =
          ∑ i, tmulLeft (Module.finBasis K L i) (coord (Module.finBasis K L) i y) :=
        adeleTensorEquiv_symm_apply (Module.finBasis K L)
      change Continuous fun y ↦ (adeleTensorEquiv K L).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ ↦
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (Module.finBasis K L i))).comp
          (continuous_coord _ i) }

@[simp]
theorem adeleTensorHomeomorph_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorHomeomorph K L t = adeleTensorEquiv K L t :=
  rfl

variable (K L) in

def adeleTensorContinuousAlgEquiv :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃A[L] 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  { adeleTensorEquiv K L with
    continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
    continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }

@[simp]
theorem adeleTensorContinuousAlgEquiv_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorContinuousAlgEquiv K L t = adeleTensorEquiv K L t :=
  rfl

scoped instance algebraAdeleRing : Algebra 𝔸[K] 𝔸[L] :=
  (adeleMap K L).toAlgebra

theorem algebraMap_adeleRing : algebraMap 𝔸[K] 𝔸[L] = adeleMap K L :=
  rfl

scoped instance continuousSMul_adeleRing : ContinuousSMul 𝔸[K] 𝔸[L] :=
  continuousSMul_of_algebraMap _ _ continuous_adeleMap

variable (K L) in

def adeleTensorAlgEquivAdele : L ⊗[K] 𝔸[K] ≃ₐ[𝔸[K]] 𝔸[L] :=
  AlgEquiv.ofRingEquiv (f := (adeleTensorEquiv K L).toRingEquiv) fun a ↦ by
    change adeleTensorEquiv K L (1 ⊗ₜ a) = adeleMap K L a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]

@[simp]
theorem adeleTensorAlgEquivAdele_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorAlgEquivAdele K L t = adeleTensorEquiv K L t :=
  rfl

variable (K L) in

def adeleTensorContinuousAlgEquivAdele :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃A[𝔸[K]] 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  { adeleTensorAlgEquivAdele K L with
    continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
    continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }

theorem isModuleTopology_adeleRing : IsModuleTopology 𝔸[K] 𝔸[L] := by
  let := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  have : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  exact IsModuleTopology.iso
    { (adeleTensorAlgEquivAdele K L).toLinearEquiv with
      continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
      continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }

variable (K L) in

def normalizedTrace : L →ₗ[K] K :=
  (finrank K L : K)⁻¹ • Algebra.trace K L

theorem normalizedTrace_one : normalizedTrace K L 1 = 1 := by
  rw [normalizedTrace, LinearMap.smul_apply, ← map_one (algebraMap K L), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one, smul_eq_mul, inv_mul_cancel₀]
  exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'

variable (K L) in

def traceRetraction : L ⊗[K] 𝔸[K] →ₗ[𝔸[K]] 𝔸[K] where
  toFun t := TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) t)
  map_add' s t := by simp only [map_add]
  map_smul' c t := by
    change _ = c * _
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L)
        ((1 ⊗ₜ c) * (l ⊗ₜ a))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, mul_smul_comm]
    | add s t hs ht => simp only [smul_add, map_add, hs, ht, mul_add]

theorem traceRetraction_one_tmul (a : 𝔸[K]) : traceRetraction K L (1 ⊗ₜ a) = a := by
  change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) (1 ⊗ₜ a)) = a
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, normalizedTrace_one, one_smul]

variable (K L) in

def adeleRetraction (y : 𝔸[L]) : 𝔸[K] :=
  traceRetraction K L ((adeleTensorEquiv K L).symm y)

theorem adeleRetraction_adeleMap (a : 𝔸[K]) : adeleRetraction K L (adeleMap K L a) = a := by
  have : (adeleTensorEquiv K L).symm (adeleMap K L a) = 1 ⊗ₜ a := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, one_mul]
  rw [adeleRetraction, this, traceRetraction_one_tmul]

theorem continuous_adeleRetraction : Continuous (adeleRetraction K L) := by
  let := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  have : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap (traceRetraction K L)).comp
    (adeleTensorHomeomorph K L).symm.continuous

theorem adeleMap_injective : Function.Injective (adeleMap K L) :=
  Function.LeftInverse.injective (g := adeleRetraction K L) adeleRetraction_adeleMap

theorem isClosedEmbedding_adeleMap : IsClosedEmbedding (adeleMap K L) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 L) L) := inferInstanceAs (T2Space
    (Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]))
  haveI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : NumberField.InfinitePlace L) → w.Completion))
  haveI : T2Space 𝔸[L] := inferInstanceAs (T2Space (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
  Function.LeftInverse.isClosedEmbedding (f := adeleRetraction K L) adeleRetraction_adeleMap
    continuous_adeleRetraction continuous_adeleMap

def finiteTmulLeft (l : L) :
    FiniteAdeleRing (𝓞 K) K →ₗ[FiniteAdeleRing (𝓞 K) K] L ⊗[K] FiniteAdeleRing (𝓞 K) K where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable (K L) in

def finiteTensorHomeomorph :
    letI := moduleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
    L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃ₜ FiniteAdeleRing (𝓞 L) L :=
  letI := moduleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 K) K)
    (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
  { toEquiv := (finiteTensorEquiv K L).toEquiv
    continuous_toFun := by
      let φ : L ⊗[K] FiniteAdeleRing (𝓞 K) K →ₛₗ[finiteAdeleMap K L] FiniteAdeleRing (𝓞 L) L :=
        { toFun := finiteTensorEquiv K L
          map_add' := map_add _
          map_smul' := fun c t ↦ by
            change finiteTensorEquiv K L ((1 ⊗ₜ c) * t) = finiteAdeleMap K L c * _
            rw [map_mul, finiteTensorEquiv_tmul, map_one, one_mul] }
      exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_finiteAdeleMap φ
    continuous_invFun := by
      have h : ∀ y, (finiteTensorEquiv K L).symm y = ∑ i, finiteTmulLeft (Module.finBasis K L i)
          (finiteCoord (Module.finBasis K L) i y) :=
        finiteTensorEquiv_symm_apply (Module.finBasis K L)
      change Continuous fun y ↦ (finiteTensorEquiv K L).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ ↦
        (IsModuleTopology.continuous_of_linearMap (finiteTmulLeft (Module.finBasis K L i))).comp
          (continuous_finiteCoord _ i) }

@[simp]
theorem finiteTensorHomeomorph_apply (t : L ⊗[K] FiniteAdeleRing (𝓞 K) K) :
    finiteTensorHomeomorph K L t = finiteTensorEquiv K L t :=
  rfl

end AdeleBaseChange

end

end GroundTheory.Global
