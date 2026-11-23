import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistence
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory.Global.SemiLocal
open scoped NumberField.LiesOver

section Disc

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {W : Type*} [AddCommGroup W] [Module A W] {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in

def HermitianForm.discUnit (h : HermitianForm F A W) (b : Basis ι A W) : Fˣ :=
  if hx : ∃ c : Fˣ, algebraMap F A c = (gram h.toSesq b).det then hx.choose else 1

end Disc

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem mem_range_finiteLocalNorm_of_eq_norm (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) (z : v.adicCompletion K ⊗[K] L)
    (hz : (x : v.adicCompletion K) = Algebra.norm (v.adicCompletion K) z) :
    x ∈ (IdeleNorm.finiteLocalNorm L v).range := by
  set p := tensorEquiv L v z
  have hp : (x : v.adicCompletion K) = ∏ w, Algebra.norm (v.adicCompletion K) (p w) := by
    rw [hz, ← GroundTheory.Global.SemiLocal.norm_pi, Algebra.norm_eq_of_algEquiv]
  have hp0 : ∀ w, p w ≠ 0 := by
    intro w h0
    apply x.ne_zero
    rw [hp]
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h0, Algebra.norm_zero])
  refine ⟨fun w ↦ Units.mk0 (p w) (hp0 w), Units.ext ?_⟩
  rw [IdeleNorm.coe_finiteLocalNorm, hp]
  rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

end LocalNorms

section InfiniteLocalNorms

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

open scoped Classical in

theorem exists_norm_tensor_eq_infiniteLocalNorm (v : InfinitePlace K)
    (y : (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    ∃ z : v.Completion ⊗[K] L,
      ((IdeleNorm.infiniteLocalNorm L v y : (v.Completion)ˣ) : v.Completion) =
        Algebra.norm v.Completion z := by
  refine ⟨(GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := L) v).symm
    (fun w ↦ (y w : (w : InfinitePlace L).Completion)), ?_⟩
  rw [← Algebra.norm_eq_of_algEquiv (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := L) v),
    AlgEquiv.apply_symm_apply, GroundTheory.Global.Algebra.norm_pi, IdeleNorm.coe_infiniteLocalNorm]

open scoped Classical in

theorem mem_range_infiniteLocalNorm_of_eq_norm (v : InfinitePlace K) (x : (v.Completion)ˣ)
    (z : v.Completion ⊗[K] L) (hz : (x : v.Completion) = Algebra.norm v.Completion z) :
    x ∈ (IdeleNorm.infiniteLocalNorm L v).range := by
  set p := GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := L) v z
  have hp : (x : v.Completion) = ∏ w, Algebra.norm v.Completion (p w) := by
    rw [hz, ← GroundTheory.Global.Algebra.norm_pi, Algebra.norm_eq_of_algEquiv]
  have hp0 : ∀ w, p w ≠ 0 := by
    intro w h0
    apply x.ne_zero
    rw [hp]
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h0, Algebra.norm_zero])
  refine ⟨fun w ↦ Units.mk0 (p w) (hp0 w), Units.ext ?_⟩
  rw [IdeleNorm.coe_infiniteLocalNorm, hp]
  rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

end InfiniteLocalNorms

section Main

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]

attribute [local instance] galCommGroup

end Main

end GroundTheory.Automorphic
