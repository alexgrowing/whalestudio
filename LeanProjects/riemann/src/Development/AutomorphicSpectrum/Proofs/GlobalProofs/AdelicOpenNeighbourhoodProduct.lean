import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CuspNbhd

open GlobalTheory.AdelicU

theorem real_mul_level_mem_nhds : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ N ∈ 𝓝 (1 : GA D V), {g : GA D V | ∃ r k : GA D V, r ∈ GinfC V ∧ r ∈ N ∧ k ∈ U ∧ k ∈ GfC V ∧ g = r * k} ∈ 𝓝 (1 : GA D V) := by
  intro D V U hU N hN
  have hr : Continuous fun g : GA D V =>
      ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) :=
    (continuous_ofInf _ _).comp (continuous_projInf _ _)
  have hk : Continuous fun g : GA D V =>
      ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) :=
    (continuous_ofFin _ _).comp (continuous_projFin _ _)
  have h1 : ∀ᶠ g : GA D V in 𝓝 1, ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) ∈ N := by
    have := hr.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this hN
  have h2 : ∀ᶠ g : GA D V in 𝓝 1, ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) ∈ U := by
    have := hk.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this (hU.mem_nhds U.one_mem)
  filter_upwards [h1, h2] with g hg1 hg2
  exact ⟨_, _, mem_infPts.2 (by simp), hg1, hg2, mem_finPts.2 (by simp),
    (ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g).symm⟩

end GlobalTheory.CompanionTheory.CuspNbhd
