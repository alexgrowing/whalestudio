import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem eventually_val_le_one (E : Type) [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 E) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun w hw => ?_
  have hw' : ¬ Valued.v ((x : E) : w.adicCompletion E) ≤ 1 := hw
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', not_le] at hw'
  exact hw'

theorem ratW_mem_KGL_eventually (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w n := by
  have hall : ∀ M : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j : Fin n,
      Valued.v (algebraMap E (w.adicCompletion E) ((M : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 := by
    intro M
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_val_le_one E _
  filter_upwards [hall δ, hall δ⁻¹] with w h1 h2
  rw [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  refine ⟨fun i j => h1 i j, fun i j => ?_⟩
  have key : (ratW n w δ)⁻¹ = ratW n w δ⁻¹ := (map_inv (ratW n w) δ).symm
  rw [key]
  exact h2 i j

end GlobalTheory.CompanionTheory.LocalHypotheses
