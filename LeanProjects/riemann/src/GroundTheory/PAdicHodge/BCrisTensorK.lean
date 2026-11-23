import Mathlib
import GroundTheory.PAdicHodge.BCrisTensorKAlg
import GroundTheory.PAdicHodge.BCrisNewton
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

section MaxUnramified

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

instance algebraMaxUnramified : Algebra (maxUnramified p K) K :=
  (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).toRingHom.toAlgebra

theorem coe_algebraMap_maxUnramified (k : maxUnramified p K) :
    ((algebraMap (maxUnramified p K) K k : K) : PadicAlgCl p) = k :=
  rfl

instance isScalarTower_maxUnramified_algCl :
    IsScalarTower (maxUnramified p K) K (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_padic_maxUnramified :
    IsScalarTower ℚ_[p] (maxUnramified p K) K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance finiteDimensional_maxUnramified [FiniteDimensional ℚ_[p] K] :
    FiniteDimensional (maxUnramified p K) K :=
  Module.Finite.of_restrictScalars_finite ℚ_[p] (maxUnramified p K) K

def unramifiedOver : IntermediateField (maxUnramified p K) (PadicAlgCl p) :=
  IntermediateField.extendScalars (inf_le_right : maxUnramified p K ≤ unramifiedClosure p)

theorem mem_unramifiedOver {x : PadicAlgCl p} : x ∈ unramifiedOver K ↔ x ∈ unramifiedClosure p :=
  Iff.rfl

instance isAlgClosure_maxUnramified : IsAlgClosure (maxUnramified p K) (PadicAlgCl p) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) (maxUnramified p K)⟩

instance normal_unramifiedOver : Normal (maxUnramified p K) (unramifiedOver K) := by
  refine IntermediateField.normal_iff_forall_map_le'.2 fun σ x hx => ?_
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  exact gal_mem_unramifiedClosure (σ.restrictScalars ℚ_[p]) hy

theorem splits_normalClosure (x : K) :
    ((minpoly (maxUnramified p K) x).map
      (algebraMap (maxUnramified p K) (IntermediateField.normalClosure (maxUnramified p K) K (PadicAlgCl p)))).Splits := by
  have hxN : algebraMap K (PadicAlgCl p) x ∈ IntermediateField.normalClosure (maxUnramified p K) K (PadicAlgCl p) :=
    (IsScalarTower.toAlgHom (maxUnramified p K) K (PadicAlgCl p)).fieldRange_le_normalClosure
      ⟨x, rfl⟩
  have h := Normal.splits (inferInstance : Normal (maxUnramified p K)
    (IntermediateField.normalClosure (maxUnramified p K) K (PadicAlgCl p))) ⟨_, hxN⟩
  rwa [IntermediateField.minpoly_eq, minpoly.algebraMap_eq (algebraMap K (PadicAlgCl p)).injective] at h

theorem linearDisjoint_unramified [FiniteDimensional ℚ_[p] K] :
    (unramifiedOver K ⊓ IntermediateField.normalClosure (maxUnramified p K) K (PadicAlgCl p)).LinearDisjoint K := by
  set K₀ := maxUnramified p K
  set N := IntermediateField.normalClosure K₀ K (PadicAlgCl p)
  set A := unramifiedOver K ⊓ N
  have : FiniteDimensional K₀ A :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_right : A ≤ N)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_right : A ≤ N))
  have : IsGalois K₀ A := ⟨⟩
  set B := (IsScalarTower.toAlgHom K₀ K (PadicAlgCl p)).fieldRange
  have : FiniteDimensional K₀ B := LinearEquiv.finiteDimensional
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K₀ K (PadicAlgCl p))).toLinearEquiv
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxU, -⟩, ⟨k, rfl⟩⟩
    rw [IntermediateField.mem_bot]
    exact ⟨⟨(k : PadicAlgCl p), k.2, (mem_unramifiedOver K).1 hxU⟩, rfl⟩
  have h := IntermediateField.linearDisjoint_iff'.1 (IntermediateField.LinearDisjoint.of_inf_eq_bot hAB)
  rw [IntermediateField.linearDisjoint_iff]
  rwa [AlgHom.fieldRange_toSubalgebra] at h

end MaxUnramified

namespace ACris

open scoped TensorProduct

section Tensor

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def unramifiedToBCrisPlus : unramifiedClosure p →ₐ[ℚ_[p]] BCrisPlus ℂ_[p] p :=
  ((AlgEquiv.ofInjective (iotaPlusAlg (p := p))
      fun _ _ h => iotaPlus_injective (K := ℂ_[p]) (p := p) h).symm :
      (iotaPlusAlg (p := p)).range →ₐ[ℚ_[p]] BCrisPlus ℂ_[p] p).comp
    (((algClToBdR p).comp (unramifiedClosure p).val).codRestrict _ fun u => unramifiedClosure_le u.2)

theorem iotaPlus_unramifiedToBCrisPlus (u : unramifiedClosure p) :
    iotaPlus ℂ_[p] p (unramifiedToBCrisPlus u) = algClToBdR p u :=
  congrArg Subtype.val ((AlgEquiv.ofInjective (iotaPlusAlg (p := p)) fun _ _ h =>
    iotaPlus_injective (K := ℂ_[p]) (p := p) h).apply_symm_apply
      ⟨algClToBdR p u, unramifiedClosure_le u.2⟩)

instance algebraMaxUnramifiedBCrisPlus : Algebra (maxUnramified p K) (BCrisPlus ℂ_[p] p) :=
  (unramifiedToBCrisPlus.comp (IntermediateField.inclusion
    (inf_le_right : maxUnramified p K ≤ unramifiedClosure p))).toRingHom.toAlgebra

instance moduleMaxUnramifiedBCrisPlus : Module (maxUnramified p K) (BCrisPlus ℂ_[p] p) :=
  Algebra.toModule

theorem iotaPlus_algebraMap_maxUnramified (k : maxUnramified p K) :
    iotaPlus ℂ_[p] p (algebraMap (maxUnramified p K) (BCrisPlus ℂ_[p] p) k) = algClToBdR p k :=
  iotaPlus_unramifiedToBCrisPlus _

instance algebraMaxUnramifiedBdRPlus : Algebra (maxUnramified p K) 𝔹 :=
  ((algClToBdR p).comp (maxUnramified p K).val).toRingHom.toAlgebra

def algToBdRPlus : K →ₐ[maxUnramified p K] 𝔹 :=
  { (algClToBdR p).toRingHom.comp (algebraMap K (PadicAlgCl p)) with commutes' := fun _ => rfl }

def iotaPlusMaxUnramified : BCrisPlus ℂ_[p] p →ₐ[maxUnramified p K] 𝔹 :=
  { iotaPlus ℂ_[p] p with commutes' := iotaPlus_algebraMap_maxUnramified K }

def tensorBCrisPlusToBdRPlus :
    K ⊗[maxUnramified p K] BCrisPlus ℂ_[p] p →ₐ[maxUnramified p K] 𝔹 :=
  Algebra.TensorProduct.lift (algToBdRPlus K) (iotaPlusMaxUnramified K) fun _ _ => Commute.all _ _

theorem tensorBCrisPlusToBdRPlus_tmul (a : K) (b : BCrisPlus ℂ_[p] p) :
    tensorBCrisPlusToBdRPlus K (a ⊗ₜ b) = algClToBdR p a * iotaPlus ℂ_[p] p b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

def algClToBdRFieldMaxUnramified : PadicAlgCl p →ₐ[maxUnramified p K] 𝔹dR :=
  { algClToBdRField p with commutes' := fun _ => rfl }

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

def iotaBMaxUnramified : BCris hε →ₐ[maxUnramified p K] 𝔹dR :=
  { iotaB hε hζ with
    commutes' := fun k => by
      change iotaB hε hζ (algebraMap (maxUnramified p K) (BCris hε) k) = _
      rw [IsScalarTower.algebraMap_apply (maxUnramified p K) (BCrisPlus ℂ_[p] p) (BCris hε),
        iotaB_algebraMap, iotaPlus_algebraMap_maxUnramified]
      rfl }

def tensorBCrisToBdR : K ⊗[maxUnramified p K] BCris hε →ₐ[maxUnramified p K] 𝔹dR :=
  Algebra.TensorProduct.lift ((algClToBdRFieldMaxUnramified K).comp
    (IsScalarTower.toAlgHom (maxUnramified p K) K (PadicAlgCl p))) (iotaBMaxUnramified K hε hζ)
    fun _ _ => Commute.all _ _

theorem tensorBCrisToBdR_tmul (a : K) (b : BCris hε) :
    tensorBCrisToBdR K hε hζ (a ⊗ₜ b) = algClToBdRField p a * iotaB hε hζ b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

def fracBCrisOver : IntermediateField (maxUnramified p K) 𝔹dR :=
  (fracBCris hε hζ).toIntermediateField fun k => (mem_fracBCris_of_mem_maxUnramified hε hζ k.2).1

def tensorFracBCrisToBdR :
    K ⊗[maxUnramified p K] fracBCrisOver K hε hζ →ₐ[maxUnramified p K] 𝔹dR :=
  Algebra.TensorProduct.lift ((algClToBdRFieldMaxUnramified K).comp
    (IsScalarTower.toAlgHom (maxUnramified p K) K (PadicAlgCl p))) (fracBCrisOver K hε hζ).val
    fun _ _ => Commute.all _ _

theorem mem_unramifiedOver_of_mem_fracBCrisOver {y : PadicAlgCl p}
    (hy : algClToBdRFieldMaxUnramified K y ∈ fracBCrisOver K hε hζ) : y ∈ unramifiedOver K :=
  mem_unramifiedClosure_of_mem_fracBCris hε hζ hy

variable [FiniteDimensional ℚ_[p] K]

theorem tensorFracBCrisToBdR_injective : Function.Injective (tensorFracBCrisToBdR K hε hζ) :=
  injective_lift_of_linearDisjoint (algClToBdRFieldMaxUnramified K) (fracBCrisOver K hε hζ)
    (unramifiedOver K) (IntermediateField.normalClosure (maxUnramified p K) K (PadicAlgCl p)) K
    (fun _ hy => mem_unramifiedOver_of_mem_fracBCrisOver K hε hζ hy) (splits_normalClosure K)
    (linearDisjoint_unramified K)

theorem tensorBCrisToBdR_injective : Function.Injective (tensorBCrisToBdR K hε hζ) :=
  injective_lift_of_forall_mem (algClToBdRFieldMaxUnramified K) (fracBCrisOver K hε hζ)
    (unramifiedOver K) (IntermediateField.normalClosure (maxUnramified p K) K (PadicAlgCl p)) K
    (fun _ hy => mem_unramifiedOver_of_mem_fracBCrisOver K hε hζ hy) (splits_normalClosure K)
    (linearDisjoint_unramified K) (iotaBMaxUnramified K hε hζ) (iotaB_injective hε hζ)
    (iotaB_mem_fracBCris hε hζ)

end Tensor

end ACris

end GroundTheory.PAdicHodge
