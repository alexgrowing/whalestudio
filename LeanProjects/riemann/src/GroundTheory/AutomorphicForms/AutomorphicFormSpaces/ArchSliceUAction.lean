import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.LeftTranslate
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

abbrev UEnv : Type _ := UniversalEnvelopingAlgebra ℝ (isExpLieAlgebra K n).lieSubalgebra

def archSlice (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    archGroup K n → ℂ :=
  fun x => φ (g * infEmb K n x)

@[simp] theorem archSlice_apply (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n)
    (x : archGroup K n) : archSlice φ g x = φ (g * infEmb K n x) := rfl

theorem archSlice_mul (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n)
    (x : archGroup K n) : archSlice φ (g * infEmb K n x) = leftTranslate x (archSlice φ g) := by
  funext y
  simp [mul_assoc]

def IsArchSmooth (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  ∀ g, (isExpLieAlgebra K n).IsSmoothFun (archSlice φ g)

variable (K n) in

def archSmooth : Submodule ℂ (AdelicGLn.AdelicGL K n → ℂ) where
  carrier := {φ | IsArchSmooth φ}
  zero_mem' _ := ((isExpLieAlgebra K n).smoothFuns (F := ℂ)).zero_mem
  add_mem' hφ hψ g := ((isExpLieAlgebra K n).smoothFuns (F := ℂ)).add_mem (hφ g) (hψ g)
  smul_mem' c _ hφ g := ((isExpLieAlgebra K n).smoothFuns (F := ℂ)).smul_mem c (hφ g)

theorem mem_archSmooth {φ : AdelicGLn.AdelicGL K n → ℂ} : φ ∈ archSmooth K n ↔ IsArchSmooth φ :=
  Iff.rfl

def sliceL (g : AdelicGLn.AdelicGL K n) :
    archSmooth K n →ₗ[ℂ] (isExpLieAlgebra K n).smoothFuns (F := ℂ) where
  toFun φ := ⟨archSlice φ g, φ.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_sliceL (g : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) :
    ((sliceL g φ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) =
      archSlice φ g := rfl

theorem sliceL_mul (g : AdelicGLn.AdelicGL K n) (x : archGroup K n) (φ : archSmooth K n) :
    sliceL (g * infEmb K n x) φ = (isExpLieAlgebra K n).leftTranslateEnd x (sliceL g φ) :=
  Subtype.ext (archSlice_mul (φ : AdelicGLn.AdelicGL K n → ℂ) g x)

def uActFun (u : UEnv K n) (φ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ :=
  fun g => ((isExpLieAlgebra K n).rightUAction u (sliceL g φ) : archGroup K n → ℂ) 1

theorem archSlice_uActFun (u : UEnv K n) (φ : archSmooth K n) (g : AdelicGLn.AdelicGL K n) :
    archSlice (uActFun u φ) g =
      ((isExpLieAlgebra K n).rightUAction u (sliceL g φ) : archGroup K n → ℂ) := by
  funext x
  simp only [archSlice_apply, uActFun, sliceL_mul]
  rw [(isExpLieAlgebra K n).rightUAction_leftTranslate_apply, mul_one]

theorem uActFun_mem (u : UEnv K n) (φ : archSmooth K n) : uActFun u φ ∈ archSmooth K n := by
  intro g
  rw [archSlice_uActFun]
  exact ((isExpLieAlgebra K n).rightUAction u (sliceL g φ)).2

def uAction : UEnv K n →ₐ[ℝ] Module.End ℂ (archSmooth K n) where
  toFun u :=
    { toFun := fun φ => ⟨uActFun u φ, uActFun_mem u φ⟩
      map_add' := fun φ ψ => by
        ext g
        simp only [uActFun, map_add, Submodule.coe_add, Pi.add_apply]
      map_smul' := fun c φ => by
        ext g
        simp only [uActFun, map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply] }
  map_one' := by
    ext φ g
    simp [uActFun]
  map_mul' u v := by
    ext φ g
    simp only [uActFun, map_mul, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    have e : sliceL g ⟨uActFun v φ, uActFun_mem v φ⟩ =
        (isExpLieAlgebra K n).rightUAction v (sliceL g φ) :=
      Subtype.ext (archSlice_uActFun v φ g)
    rw [e]
  map_zero' := by
    ext φ g
    simp [uActFun]
  map_add' u v := by
    ext φ g
    simp [uActFun]
  commutes' r := by
    ext φ g
    simp [uActFun, Algebra.algebraMap_eq_smul_one]

theorem coe_uAction (u : UEnv K n) (φ : archSmooth K n) :
    ((uAction u φ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = uActFun u φ := rfl

theorem archSlice_uAction (u : UEnv K n) (φ : archSmooth K n) (g : AdelicGLn.AdelicGL K n) :
    archSlice (uAction u φ : AdelicGLn.AdelicGL K n → ℂ) g =
      ((isExpLieAlgebra K n).rightUAction u (sliceL g φ) : archGroup K n → ℂ) :=
  archSlice_uActFun u φ g

theorem uAction_ι_apply (X : (isExpLieAlgebra K n).lieSubalgebra) (φ : archSmooth K n)
    (g : AdelicGLn.AdelicGL K n) :
    (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ : AdelicGLn.AdelicGL K n → ℂ) g =
      (isExpLieAlgebra K n).rightDeriv ((isExpLieAlgebra K n).ofLie X) (archSlice φ g) 1 := by
  rw [coe_uAction]
  show ((isExpLieAlgebra K n).rightUAction (UniversalEnvelopingAlgebra.ι ℝ X) (sliceL g φ) :
    archGroup K n → ℂ) 1 = _
  rw [(isExpLieAlgebra K n).rightUAction_ι]
  rfl

end AutomorphicForm

end

end GroundTheory.Automorphic
