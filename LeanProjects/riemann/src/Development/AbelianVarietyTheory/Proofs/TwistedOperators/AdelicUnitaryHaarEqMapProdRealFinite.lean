import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarSplit
open scoped ENNReal NNReal

theorem haar_eq_map_prod : ∀ (D : D7) (Y : HSp D) (ν : Measure (GA D Y)), ν.IsHaarMeasure → ∃ (m : Measure (GinfC Y)) (μ : Measure (GfC Y)), m.IsHaarMeasure ∧ μ.IsHaarMeasure ∧ SigmaFinite m ∧ SigmaFinite μ ∧ MeasurableEmbedding (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) ∧ ν = (m.prod μ).map (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) := by
  intro D Y ν hν
  haveI : LocallyCompactSpace (GinfC Y) := (GlobalTheory.AdelicSplit.isClosed_GinfC' Y).locallyCompactSpace
  haveI : LocallyCompactSpace (GfC Y) := (GlobalTheory.AdelicSplit.isClosed_GfC' Y).locallyCompactSpace
  set e := GlobalTheory.AdelicSplit.splitEquiv Y with he_def
  have he : (⇑e : GinfC Y × GfC Y → GA D Y) = fun q => (q.1 : GA D Y) * q.2 := rfl
  let m₀ : Measure (GinfC Y) := Measure.haar
  let μ : Measure (GfC Y) := Measure.haar
  haveI hρ : ((m₀.prod μ).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ e
  set c := Measure.haarScalarFactor ν ((m₀.prod μ).map e) with hc_def
  have hc : ν = c • (m₀.prod μ).map e := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  haveI hm : ((c : ℝ≥0∞) • m₀).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (by simpa using hc0) ENNReal.coe_ne_top
  refine ⟨(c : ℝ≥0∞) • m₀, μ, hm, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← he]; exact e.toHomeomorph.measurableEmbedding
  · rw [← he, Measure.prod_smul_left, Measure.map_smul, hc, ENNReal.smul_def]

end GlobalTheory.HaarSplit
