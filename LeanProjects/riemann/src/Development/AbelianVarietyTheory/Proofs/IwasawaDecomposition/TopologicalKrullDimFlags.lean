import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimAffinePointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCellMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InjectiveCellMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenMapCellMapStatement

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

theorem card_lowerPairs (d : ℕ) : Fintype.card {p : Fin d × Fin d // p.2 < p.1} = d * (d - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.sum_range_id, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem card_cellIdx {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] {n : ℕ} (hn : ∀ i, finrank k (V i) = n) :
    Fintype.card (CellIdx k V) = Fintype.card ι * (n * (n - 1) / 2) := by
  have h1 : Fintype.card (CellIdx k V) =
      ∑ i, Fintype.card {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1} := by
    unfold CellIdx
    convert Fintype.card_sigma (α := fun i => {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1})
  rw [h1]
  simp only [card_lowerPairs, hn, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem isOpenEmbedding_cellMap {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Topology.IsOpenEmbedding (cellMap b) :=
  .of_continuous_injective_isOpenMap (GlobalTheory.T.continuous_cellMap' k ι V b) (GlobalTheory.T.injective_cellMap k ι V b) (GlobalTheory.T.isOpenMap_cellMap' k ι V b)

theorem topologicalKrullDim_flags (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ)
    (hn : ∀ i, finrank k (V i) = n) :
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) := by
  have hU : topologicalKrullDim (Set.univ : Set (Flags k V)) = topologicalKrullDim (Flags k V) :=
    (Homeomorph.Set.univ (Flags k V)).isHomeomorph.topologicalKrullDim_eq
  rw [← hU, ← card_cellIdx (k := k) (V := V) hn, ← GlobalTheory.T.topologicalKrullDim_affine_points k (CellIdx k V)]
  refine GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun F _ => ?_
  obtain ⟨b, rfl⟩ := flags_surjective F
  have he := isOpenEmbedding_cellMap b
  refine ⟨Set.range (cellMap b), he.isOpen_range, ⟨0, cellMap_zero b⟩, ?_⟩
  rw [Set.inter_univ]
  exact GlobalTheory.topologicalKrullDim_eq_of_isEmbedding he.isEmbedding rfl

example : ∀ (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ), (∀ i, finrank k (V i) = n) →
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) :=
  topologicalKrullDim_flags

end GlobalTheory.FlagPts
