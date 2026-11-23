import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBoxStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem extY_map_infPart_eq_zero {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (a : Mx D T.rank ρ) (ha : a.map (infPart D) = 0) : (d.extY T a).map (infPart D) = 0 := by
  rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]

theorem mixS_support_inBox : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w, d.mixS T ψ v.μ v.𝓕 f x w ≠ 0 → InBox K x := by
  intro D ψ hψ S S₀ T ρ d v U hU
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.T.finiteAnnihilator_open_subgroup_in_box D ψ hψ S S₀ T ρ d U hU
  refine ⟨K, hK, fun f hf x w hne => hbox x fun a ha haU => ?_⟩
  have hY := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf.1).2.1 x a
  rw [hf.2 _ haU (extY_map_infPart_eq_zero d T a ha)] at hY
  have hw := congrFun hY w
  rw [Pi.smul_apply, smul_eq_mul] at hw
  have h1 : (ψ (symplO S T (d.extX T x) (d.extY T a)) - 1) * d.mixS T ψ v.μ v.𝓕 f x w = 0 := by
    rw [sub_mul, one_mul, ← hw, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hne)

end GlobalTheory.Unf
