import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinedBoxDisjointCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refined_box_disjoint_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [Fintype D] (ϖ : kˣ), IsUnif ϖ → ∀ (r r' : A → D → ℕ), (∀ i j, r i j ≤ r' i j) → ∃ S : Finset (Matrix A D k), ∀ C : Matrix A D k, ebox ϖ C r = (⋃ x ∈ S, ebox ϖ (C + x) r') ∧ (↑S : Set (Matrix A D k)).PairwiseDisjoint (fun x => ebox ϖ (C + x) r') := by
  first | exact @GlobalTheory.NormalCore.ebox_eq_biUnion_disjoint | exact GlobalTheory.NormalCore.ebox_eq_biUnion_disjoint | (intros; apply GlobalTheory.NormalCore.ebox_eq_biUnion_disjoint <;> assumption)
