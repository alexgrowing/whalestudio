import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentHolomorphicAtlas
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSNCAtlasOfIsEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt GlobalTheory.SNCComp
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_component_holomorphic_atlas : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (B : FinHolAtlas (n + 1) Y) (X : Type) [TopologicalSpace X] (μ : Y → X) (q r : ℕ)
    (L : Fin q → LocPot X) (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ),
    IsJointSNC B μ L t W e → ∀ k, ∃ C : FinHolAtlas n (W k), HoloMap C B Subtype.val ∧
      GlobalTheory.SNCComp.IsSNCAtlas B μ L t W e k C := by
  first | exact @GlobalTheory.SNCComp.CompAtlas.exists_isSNCAtlas | exact GlobalTheory.SNCComp.CompAtlas.exists_isSNCAtlas | (intros; apply GlobalTheory.SNCComp.CompAtlas.exists_isSNCAtlas <;> assumption)
