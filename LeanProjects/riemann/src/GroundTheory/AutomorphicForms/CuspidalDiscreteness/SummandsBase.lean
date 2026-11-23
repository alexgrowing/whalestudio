import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing
import GroundTheory.AutomorphicForms.GKModules.Garding

open MeasureTheory Set Filter Topology Function

namespace GroundTheory.Automorphic

noncomputable section

namespace BanachRep

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def comp (π : BanachRep G E) (f : G' →* G) (hf : Continuous f) : BanachRep G' E where
  toHom := π.toHom.comp f
  continuous_orbit' v := (π.continuous_orbit v).comp hf

@[simp] theorem comp_apply (π : BanachRep G E) (f : G' →* G) (hf : Continuous f) (g : G') :
    π.comp f hf g = π (f g) := rfl

end BanachRep

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

def archP : archGroup K n →* Reduction.normOneGL K n :=
  (archProj K n).comp (archGroup K n).subtype

@[simp] theorem archimedeanProjection_apply (a : archGroup K n) : archP K n a = archProj K n (a : ArchUnits K n) := rfl

theorem continuous_archP : Continuous (archP K n) :=
  continuous_archProj.comp continuous_subtype_val

variable (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]

def cuspBanachRep : BanachRep (Reduction.normOneGL K n) (cuspidalL2 μ) :=
  BanachRep.ofUnitary (cuspRep μ)

def archRep : BanachRep (archGroup K n) (cuspidalL2 μ) :=
  BanachRep.comp (cuspBanachRep μ) (archP K n) continuous_archP

end CuspidalSpectrum

end

end GroundTheory.Automorphic
