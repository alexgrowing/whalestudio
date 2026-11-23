import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem mixS_rankZero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0)
    (μ : Measure (Mx D T.rank 0)) (𝓕 : Set (Mx D T.rank 0)) (hμ : IsCovolOne (ratMx D T.rank 0) μ 𝓕)
    (f : WO S T → ℂ) (x : Mx D T.rank 0) : d.mixS T ψ μ 𝓕 f x = fun w => f (d.ext0 T w) := by
  funext w
  have h1 : ∀ a : Mx D T.rank 0,
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 = f (d.ext0 T w) := by
    intro a
    rw [d.integrandS_eq, Subsingleton.elim a 0, Subsingleton.elim x 0, map_zero, map_zero, symplOH_zero_left,
      AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]
  simp only [HypDec.mixS, h1]
  rw [MeasureTheory.setIntegral_const]
  simp [Measure.real, hμ.2.2]

theorem mixT_rankZero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (d : HypDec T T₀ 0)
    (μ : Measure (Mx D 0 S.rank)) (𝓕 : Set (Mx D 0 S.rank)) (hμ : IsCovolOne (ratMx D 0 S.rank) μ 𝓕)
    (f : WO S T → ℂ) (y : Mx D S.rank 0) : d.mixT S ψ μ 𝓕 f y = fun w => f (d.inc0 S w) := by
  funext w
  have h1 : ∀ ξ : Mx D 0 S.rank,
      heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w) f)) 0 = f (d.inc0 S w) := by
    intro ξ
    rw [d.integrandT_eq, Subsingleton.elim ξ 0, Subsingleton.elim y 0, map_zero, map_zero, symplOH_zero_left,
      AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]
  simp only [HypDec.mixT, h1]
  rw [MeasureTheory.setIntegral_const]
  simp [Measure.real, hμ.2.2]

theorem rankZero_trivial {D : D7} (S S₀ : HSp D) (d : HypDec S S₀ 0) :
    (∀ a, d.levi a = 1) ∧ (∀ b, d.nB b = 1) ∧ ∀ c, d.nC c = 1 := by
  refine ⟨fun a => ?_, fun b => ?_, fun c => ?_⟩
  · rw [Subsingleton.elim a 1, map_one]
  · rw [Subsingleton.elim b 0, d.nB_zero]
  · rw [Subsingleton.elim c 0, d.nC_zero]

theorem mixRankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (S S₀ T : HSp D) (d : HypDec S S₀ 0) (μ : Measure (Mx D T.rank 0)) (𝓕 : Set (Mx D T.rank 0)), IsCovolOne (ratMx D T.rank 0) μ 𝓕 → ∀ f x, d.mixS T ψ μ 𝓕 f x = fun w => f (d.ext0 T w)) ∧ (∀ (S T T₀ : HSp D) (d : HypDec T T₀ 0) (μ : Measure (Mx D 0 S.rank)) (𝓕 : Set (Mx D 0 S.rank)), IsCovolOne (ratMx D 0 S.rank) μ 𝓕 → ∀ f y, d.mixT S ψ μ 𝓕 f y = fun w => f (d.inc0 S w)) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ 0), (∀ a, d.levi a = 1) ∧ (∀ b, d.nB b = 1) ∧ ∀ c, d.nC c = 1 := by
  intro D ψ
  exact ⟨fun S S₀ T d μ 𝓕 hμ f x => mixS_rankZero ψ S S₀ T d μ 𝓕 hμ f x,
    fun S T T₀ d μ 𝓕 hμ f y => mixT_rankZero ψ S T T₀ d μ 𝓕 hμ f y,
    fun S S₀ d => rankZero_trivial S S₀ d⟩

end GlobalTheory.Unf

end
