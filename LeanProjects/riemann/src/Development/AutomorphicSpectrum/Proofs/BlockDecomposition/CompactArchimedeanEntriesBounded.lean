import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_entries_bounded_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J))
    (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ B := by
  classical
  have hb : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ∃ b : ℝ, ∀ g ∈ C, ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ b := by
    intro w τ i j
    have hc : Continuous fun g : GAd σ J => ‖archMat σ J τ (projArch σ J w g) i j‖ :=
      (((GlobalTheory.Orb.continuous_archMat σ J τ).comp (continuous_projArch σ J w)).matrix_elem i j).norm
    obtain ⟨b, hb⟩ := hC.bddAbove_image hc.continuousOn
    exact ⟨b, fun g hg => hb ⟨g, hg, rfl⟩⟩
  choose b hb using hb
  haveI : Fintype (InfinitePlace F) := inferInstance
  refine ⟨∑ w : InfinitePlace F, ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|,
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _, fun g hg w τ i j => ?_⟩
  calc ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ b w τ i j := hb w τ i j g hg
    _ ≤ |b w τ i j| := le_abs_self _
    _ ≤ ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun j => |b w τ i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun i => ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun τ => ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ τ)
    _ ≤ ∑ w : InfinitePlace F, ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)

end GlobalTheory.CompanionTheory.CFin
