import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteFactor
import GroundTheory.AutomorphicForms.SmoothRep

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep (normOneGL K n) H)

abbrev archRep : UnitaryRep (ArchUnits K n) H := σ.compHom (archProj K n) continuous_archProj

variable (V₀ : Submodule ℂ H) [CompleteSpace V₀] (hV₀ : (archRep σ).IsInvariant V₀)

def archType : UnitaryRep (ArchUnits K n) V₀ := (archRep σ).restrict V₀ hV₀

def homArch : Submodule ℂ (V₀ →L[ℂ] H) := (archType σ V₀ hV₀).intertwiners (archRep σ)

theorem finProj_comp_mem_homArch (w : AdelicGLn.FiniteAdelicGL K n) {S : V₀ →L[ℂ] H}
    (hS : S ∈ homArch σ V₀ hV₀) : σ (finProj K n w) ∘L S ∈ homArch σ V₀ hV₀ := by
  intro A v
  show σ (finProj K n w) (S (archType σ V₀ hV₀ A v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [hS A v]
  show σ (finProj K n w) (σ (archProj K n A) (S v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, finProj_mul_archProj_comm]

def HomSpace : Type _ := homArch σ V₀ hV₀

instance : AddCommGroup (HomSpace σ V₀ hV₀) := inferInstanceAs (AddCommGroup (homArch σ V₀ hV₀))

instance : Module ℂ (HomSpace σ V₀ hV₀) := inferInstanceAs (Module ℂ (homArch σ V₀ hV₀))

def HomSpace.op (S : HomSpace σ V₀ hV₀) : V₀ →L[ℂ] H := (S : homArch σ V₀ hV₀).1

def finRep : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (HomSpace σ V₀ hV₀) where
  toFun w :=
    { toFun := fun S => (⟨σ (finProj K n w) ∘L (S : homArch σ V₀ hV₀).1,
        finProj_comp_mem_homArch σ V₀ hV₀ w (S : homArch σ V₀ hV₀).2⟩ : homArch σ V₀ hV₀)
      map_add' := fun S S' => Subtype.ext (ContinuousLinearMap.comp_add _ _ _)
      map_smul' := fun c S => Subtype.ext (ContinuousLinearMap.comp_smul _ _ _) }
  map_one' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n 1) ∘L (S : homArch σ V₀ hV₀).1 = (S : homArch σ V₀ hV₀).1
    rw [map_one, UnitaryRep.map_one]
    exact ContinuousLinearMap.id_comp _
  map_mul' w w' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n (w * w')) ∘L (S : homArch σ V₀ hV₀).1 =
      σ (finProj K n w) ∘L (σ (finProj K n w') ∘L (S : homArch σ V₀ hV₀).1)
    rw [map_mul, UnitaryRep.map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

def FinitePartSpace : Type _ := smoothVectors (finRep σ V₀ hV₀)

instance : AddCommGroup (FinitePartSpace σ V₀ hV₀) :=
  inferInstanceAs (AddCommGroup (smoothVectors (finRep σ V₀ hV₀)))

instance : Module ℂ (FinitePartSpace σ V₀ hV₀) :=
  inferInstanceAs (Module ℂ (smoothVectors (finRep σ V₀ hV₀)))

def finitePart : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (FinitePartSpace σ V₀ hV₀) :=
  smoothPart (finRep σ V₀ hV₀)

def fpOp (S : FinitePartSpace σ V₀ hV₀) : V₀ →L[ℂ] H :=
  HomSpace.op σ V₀ hV₀ (S : smoothVectors (finRep σ V₀ hV₀)).1

theorem fpOp_finitePart (w : AdelicGLn.FiniteAdelicGL K n) (S : FinitePartSpace σ V₀ hV₀) :
    fpOp σ V₀ hV₀ (finitePart σ V₀ hV₀ w S) = σ (finProj K n w) ∘L fpOp σ V₀ hV₀ S := rfl

theorem fpOp_mem_homArch (S : FinitePartSpace σ V₀ hV₀) : fpOp σ V₀ hV₀ S ∈ homArch σ V₀ hV₀ :=
  ((S : smoothVectors (finRep σ V₀ hV₀)).1 : homArch σ V₀ hV₀).2

section Admissible

variable {σ V₀}
variable {U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hV₀U : V₀ ≤ fixedSubspace σ U₀)

include hV₀ hV₀U in

theorem isInvariant_levelSubgroup {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hU' : U' ≤ U₀) :
    (σ.compHom (levelSubgroup K n U').subtype continuous_subtype_val).IsInvariant V₀ := by
  rintro ⟨x, hx⟩ v hv
  obtain ⟨A, u, hu, rfl⟩ := exists_of_mem_levelSubgroup hx
  show σ (archProj K n A * finProj K n u) v ∈ V₀
  rw [UnitaryRep.map_mul_apply, hV₀U hv u (hU' hu)]
  exact hV₀ A v hv

def levelType {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hU' : U' ≤ U₀) :
    UnitaryRep (levelSubgroup K n U') V₀ :=
  (σ.compHom (levelSubgroup K n U').subtype continuous_subtype_val).restrict V₀
    (isInvariant_levelSubgroup hV₀ hV₀U hU')

theorem fpOp_fixed {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)}
    (S : fixedVectors (finitePart σ V₀ hV₀) U') {u : AdelicGLn.FiniteAdelicGL K n} (hu : u ∈ U')
    (v : V₀) : σ (finProj K n u) (fpOp σ V₀ hV₀ S.1 v) = fpOp σ V₀ hV₀ S.1 v := by
  have h := congrArg (fpOp σ V₀ hV₀) (S.2 u hu)
  rw [fpOp_finitePart] at h
  exact congrArg (fun T : V₀ →L[ℂ] H => T v) h

def toLevelHom {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hU' : U' ≤ U₀) :
    fixedVectors (finitePart σ V₀ hV₀) U' →ₗ[ℂ]
      (levelType hV₀ hV₀U hU').intertwiners (levelRep σ U') where
  toFun S := ⟨(fpOp σ V₀ hV₀ S.1).codRestrict (fixedSubspace σ U')
      (fun v u hu => fpOp_fixed hV₀ S hu v),
    by
      rintro ⟨x, hx⟩ v
      obtain ⟨A, u, hu, rfl⟩ := exists_of_mem_levelSubgroup hx
      refine Subtype.ext ?_
      have hvA : σ (archProj K n A * finProj K n u) v = σ (archProj K n A) v := by
        rw [UnitaryRep.map_mul_apply, hV₀U v.2 u (hU' hu)]
      have e : (levelType hV₀ hV₀U hU' ⟨_, hx⟩ v : V₀) = archType σ V₀ hV₀ A v := Subtype.ext hvA
      calc fpOp σ V₀ hV₀ S.1 (levelType hV₀ hV₀U hU' ⟨_, hx⟩ v)
          = fpOp σ V₀ hV₀ S.1 (archType σ V₀ hV₀ A v) := congrArg _ e
        _ = σ (archProj K n A) (fpOp σ V₀ hV₀ S.1 v) := fpOp_mem_homArch σ V₀ hV₀ S.1 A v
        _ = σ (archProj K n A * finProj K n u) (fpOp σ V₀ hV₀ S.1 v) := by
            rw [UnitaryRep.map_mul_apply, fpOp_fixed hV₀ S hu v]⟩
  map_add' S S' := rfl
  map_smul' c S := rfl

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

end Admissible

end MultiplicityOne

end

end GroundTheory.Automorphic
