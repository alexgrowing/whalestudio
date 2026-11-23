import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

def traceHerm (h : HermitianForm F E W) (v : Basis ι E W) : LinearMap.BilinForm ℚ (ι → E) :=
  LinearMap.mk₂ ℚ
    (fun y z => Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)))
    (fun y₁ y₂ z => by simp only [map_add, LinearMap.add_apply])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • y) = (algebraMap ℚ E c) • v.equivFun.symm y := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      have e2 : conjHom F E (algebraMap ℚ E c) = algebraMap ℚ E c :=
        RingHom.map_rat_algebraMap _ _
      rw [e1, LinearMap.map_smulₛₗ₂, e2, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul,
        smul_eq_mul])
    (fun y z₁ z₂ => by simp only [map_add])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • z) = (algebraMap ℚ E c) • v.equivFun.symm z := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      rw [e1, LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])

theorem traceHerm_apply (h : HermitianForm F E W) (v : Basis ι E W) (y z : ι → E) :
    traceHerm h v y z = Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)) := rfl

def TraceHermNondegenerate.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  (traceHerm h v).Nondegenerate

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
