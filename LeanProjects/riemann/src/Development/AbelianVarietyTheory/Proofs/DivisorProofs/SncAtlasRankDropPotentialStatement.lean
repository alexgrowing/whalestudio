import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtlasRankDropPotential
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSNCAtlasOfIsEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt GlobalTheory.SNCComp
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_atlas_rank_drop_potential : ∀ (d n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas d X)
    (B : FinHolAtlas (n + 1) Y) (μ : Y → X) (hμ : HoloMap B A μ) (q r : ℕ) (L : Fin q → LocPot X)
    (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) (k : Fin r)
    (C : FinHolAtlas n (W k)), HoloMap C B Subtype.val → GlobalTheory.SNCComp.IsSNCAtlas B μ L t W e k C →
    RankDropAlong A μ B (W k) → ∀ Φ : Fin n → LocPot X, (∀ i, IsPotential A (Φ i)) →
    ∀ g : W k → ℝ, mInt C (fun i => ((Φ i).pullback μ hμ.1).pullback Subtype.val continuous_subtype_val) g = 0 := by
  first | exact @GlobalTheory.SNCRankDrop.mInt_eq_zero_of_rankDropAlong | exact GlobalTheory.SNCRankDrop.mInt_eq_zero_of_rankDropAlong | (intros; apply GlobalTheory.SNCRankDrop.mInt_eq_zero_of_rankDropAlong <;> assumption)
