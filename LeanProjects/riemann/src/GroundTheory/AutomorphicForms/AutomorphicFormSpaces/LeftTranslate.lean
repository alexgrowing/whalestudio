import Mathlib
import GroundTheory.AutomorphicForms.GKModules.GKModule
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.GKModules.Casimir

namespace GroundTheory.Automorphic

open Set Filter Topology

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

def leftTranslate {M : Type*} [Mul M] {F : Type*} (a : M) (f : M → F) (g : M) : F := f (a * g)

@[simp] theorem leftTranslate_apply {M : Type*} [Mul M] {F : Type*} (a : M) (f : M → F) (g : M) :
    leftTranslate a f g = f (a * g) := rfl

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem isSmoothFun_leftTranslate {f : G → F} (hf : h.IsSmoothFun f) (a : G) :
    h.IsSmoothFun (leftTranslate a f) := by
  rw [h.isSmoothFun_iff] at hf ⊢
  intro g
  simpa only [leftTranslate, mul_assoc] using hf (a * g)

theorem rightDeriv_leftTranslate (X : 𝔤) (f : G → F) (a : G) :
    h.rightDeriv X (leftTranslate a f) = leftTranslate a (h.rightDeriv X f) := by
  funext g
  simp only [rightDeriv, leftTranslate, mul_assoc]

def leftTranslateEnd (a : G) : Module.End ℂ (h.smoothFuns (F := F)) where
  toFun f := ⟨leftTranslate a f, h.isSmoothFun_leftTranslate f.2 a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_leftTranslateEnd (a : G) (f : h.smoothFuns (F := F)) :
    ((h.leftTranslateEnd a f : h.smoothFuns (F := F)) : G → F) = leftTranslate a f := rfl

theorem leftTranslateEnd_mul (a b : G) :
    h.leftTranslateEnd (F := F) a * h.leftTranslateEnd b = h.leftTranslateEnd (b * a) :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [leftTranslate, mul_assoc])

theorem leftTranslateEnd_one : h.leftTranslateEnd (F := F) 1 = 1 :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [leftTranslate])

theorem leftTranslateEnd_inv_mul (a : G) :
    h.leftTranslateEnd (F := F) a⁻¹ * h.leftTranslateEnd a = 1 := by
  rw [leftTranslateEnd_mul, mul_inv_cancel, leftTranslateEnd_one]

theorem leftTranslateEnd_mul_inv (a : G) :
    h.leftTranslateEnd (F := F) a * h.leftTranslateEnd a⁻¹ = 1 := by
  rw [leftTranslateEnd_mul, inv_mul_cancel, leftTranslateEnd_one]

theorem rightDerivEnd_mul_leftTranslateEnd (X : 𝔤) (a : G) :
    h.rightDerivEnd (F := F) X * h.leftTranslateEnd a = h.leftTranslateEnd a * h.rightDerivEnd X :=
  LinearMap.ext fun f => Subtype.ext (h.rightDeriv_leftTranslate X (f : G → F) a)

def conjLeft (a : G) :
    Module.End ℂ (h.smoothFuns (F := F)) →ₐ[ℝ] Module.End ℂ (h.smoothFuns (F := F)) where
  toFun T := h.leftTranslateEnd a⁻¹ * T * h.leftTranslateEnd a
  map_one' := by rw [mul_one, leftTranslateEnd_inv_mul]
  map_mul' S T := by
    calc h.leftTranslateEnd a⁻¹ * (S * T) * h.leftTranslateEnd a
        = h.leftTranslateEnd a⁻¹ * S * (h.leftTranslateEnd a * h.leftTranslateEnd a⁻¹) * T *
            h.leftTranslateEnd a := by rw [leftTranslateEnd_mul_inv]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' S T := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
    rw [leftTranslateEnd_inv_mul]

theorem conjLeft_comp_rightUAction (a : G) :
    (h.conjLeft (F := F) a).comp (h.rightUAction (F := F)) = h.rightUAction (F := F) := by
  refine UniversalEnvelopingAlgebra.hom_ext ℝ (A := Module.End ℂ (h.smoothFuns (F := F))) ?_
  apply LieHom.ext
  intro X
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.coe_comp,
    rightUAction_ι]
  simp only [conjLeft, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_assoc, rightDerivEnd_mul_leftTranslateEnd, ← mul_assoc, leftTranslateEnd_inv_mul,
    one_mul]

theorem rightUAction_mul_leftTranslateEnd (a : G)
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.rightUAction (F := F) u * h.leftTranslateEnd a = h.leftTranslateEnd a * h.rightUAction u := by
  have := congrArg (fun φ => φ u) (h.conjLeft_comp_rightUAction (F := F) a)
  simp only [AlgHom.comp_apply, conjLeft, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk] at this
  calc h.rightUAction (F := F) u * h.leftTranslateEnd a
      = h.leftTranslateEnd a * (h.leftTranslateEnd a⁻¹ * h.rightUAction u *
          h.leftTranslateEnd a) := by
        rw [← mul_assoc, ← mul_assoc, leftTranslateEnd_mul_inv, one_mul]
    _ = h.leftTranslateEnd a * h.rightUAction u := by rw [this]

theorem rightUAction_leftTranslate_apply (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra)
    (a : G) (f : h.smoothFuns (F := F)) (g : G) :
    (h.rightUAction u (h.leftTranslateEnd a f) : G → F) g = (h.rightUAction u f : G → F) (a * g) :=
  congrArg (fun T : Module.End ℂ (h.smoothFuns (F := F)) => (T f : G → F) g)
    (h.rightUAction_mul_leftTranslateEnd a u)

end IsExpLieAlgebra

end GroundTheory.Automorphic
