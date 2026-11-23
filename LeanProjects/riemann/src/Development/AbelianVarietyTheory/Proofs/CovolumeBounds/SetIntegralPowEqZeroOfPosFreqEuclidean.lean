import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummablePiProd

open MeasureTheory Filter Topology
open scoped Real FourierTransform Pointwise

namespace GlobalTheory

section Products

variable {ι : Type*} [Fintype ι] {J : ι → Type*}

theorem summable_prod_tuples {u : ∀ i, J i → ℝ} (h0 : ∀ i j, 0 ≤ u i j) (hu : ∀ i, Summable (u i)) :
    Summable fun t : ∀ i, J i => ∏ i, u i (t i) := by
  first
  | exact @_root_.GlobalTheory.SummablePiProd.summable_pi_prod
  | exact _root_.GlobalTheory.SummablePiProd.summable_pi_prod
  | (apply _root_.GlobalTheory.SummablePiProd.summable_pi_prod <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummablePiProd.summable_pi_prod <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummablePiProd.summable_pi_prod <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummablePiProd.summable_pi_prod ..)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace 𝕜 (V i)] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

theorem summable_norm_multilinear_tuples (M : ContinuousMultilinearMap 𝕜 V W)
    {x : ∀ i, J i → V i} (hx : ∀ i, Summable fun j => ‖x i j‖) :
    Summable fun t : ∀ i, J i => ‖M fun i => x i (t i)‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => M.le_opNorm _)
    ((summable_prod_tuples (fun i j => norm_nonneg (x i j)) hx).mul_left ‖M‖)

theorem hasSum_multilinear_tuples [CompleteSpace W] (M : ContinuousMultilinearMap 𝕜 V W)
    {x : ∀ i, J i → V i} {A : ∀ i, V i} (hx : ∀ i, Summable fun j => ‖x i j‖)
    (hA : ∀ i, HasSum (x i) (A i)) :
    HasSum (fun t : ∀ i, J i => M fun i => x i (t i)) (M A) := by
  classical
  have hs := (summable_norm_multilinear_tuples M hx).of_norm.hasSum
  have hpi : Tendsto (fun s : ∀ i, Finset (J i) => Fintype.piFinset s) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone (fun s s' hss => Fintype.piFinset_subset _ _ hss)
      fun T => ⟨fun i => T.image fun t => t i, fun t ht => ?_⟩
    exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
  have h1 : Tendsto (fun s : ∀ i, Finset (J i) => M fun i => ∑ j ∈ s i, x i j) atTop (𝓝 (M A)) := by
    refine (M.cont.tendsto A).comp (tendsto_pi_nhds.2 fun i => ?_)
    refine Tendsto.comp (hA i) (g := fun s => ∑ j ∈ s, x i j) (f := fun s : ∀ i, Finset (J i) => s i) ?_
    refine tendsto_atTop_atTop_of_monotone (fun s s' hss => hss i) fun T => ?_
    exact ⟨Function.update (fun _ => ∅) i T, by simp⟩
  have h2 : Tendsto (fun s : ∀ i, Finset (J i) => M fun i => ∑ j ∈ s i, x i j) atTop
      (𝓝 (∑' t : ∀ i, J i, M fun i => x i (t i))) := by
    have hs' : Tendsto (fun s : Finset (∀ i, J i) => ∑ t ∈ s, M fun i => x i (t i)) atTop
        (𝓝 (∑' t : ∀ i, J i, M fun i => x i (t i))) := hs
    exact (hs'.comp hpi).congr fun s => (M.map_sum_finset x s).symm
  rwa [tendsto_nhds_unique h1 h2]

end Products

section Banach

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {R : Type*} [NormedCommRing R] [NormedAlgebra 𝕜 R]
  [CompleteSpace R] {J : Type*}

end Banach

section Characters

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] {μ : Measure G}
  [μ.IsAddLeftInvariant] {L : AddSubgroup G} [Countable L] {D : Set G}

end Characters

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {D : Set E}

end Lattice

section Orthant

end Orthant

end GlobalTheory
