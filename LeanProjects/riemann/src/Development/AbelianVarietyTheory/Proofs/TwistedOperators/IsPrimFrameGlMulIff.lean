import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.PrimFrameLeft

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]

theorem row_mul_eq_sum (M : Matrix A A k) (Y : Matrix A D k) (i : A) :
    (M * Y).row i = ∑ l, M i l • Y.row l := by
  funext j
  simp [Matrix.mul_apply, Finset.sum_apply, Matrix.row]

theorem span_O_row_mul_le (M : Matrix A A k) (hM : ∀ i j, M i j ∈ 𝒪[k]) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (M * Y).row) ≤ Submodule.span 𝒪[k] (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ (⟨M i l, hM i l⟩ : 𝒪[k]) (Submodule.subset_span ⟨l, rfl⟩)

theorem span_k_row_mul_le (M : Matrix A A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (M * Y).row) ≤ Submodule.span k (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem span_O_row_gl_mul (g : GL A k) (hg : g ∈ KO k A) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (g.val * Y).row) = Submodule.span 𝒪[k] (Set.range Y.row) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  refine le_antisymm (span_O_row_mul_le _ h1 Y) ?_
  have := span_O_row_mul_le _ h2 (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem span_k_row_gl_mul (g : GL A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (g.val * Y).row) = Submodule.span k (Set.range Y.row) := by
  refine le_antisymm (span_k_row_mul_le _ Y) ?_
  have := span_k_row_mul_le (g⁻¹).val (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem mem_matLat_iff_span_le (Λ : Submodule 𝒪[k] (D → k)) (Y : Matrix A D k) :
    Y ∈ matLat A Λ ↔ Submodule.span 𝒪[k] (Set.range Y.row) ≤ Λ := by
  rw [Submodule.span_le, mem_matLat]
  exact ⟨fun h => by rintro _ ⟨i, rfl⟩; exact h i, fun h i => h ⟨i, rfl⟩⟩

theorem isPrimFrame_gl_mul_iff (Λ : Submodule 𝒪[k] (D → k)) (g : GL A k) (hg : g ∈ KO k A)
    (Y : Matrix A D k) : IsPrimFrame Λ (g.val * Y) ↔ IsPrimFrame Λ Y := by
  have hrank : (g.val * Y).rank = Y.rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  unfold IsPrimFrame
  rw [hrank, mem_matLat_iff_span_le, mem_matLat_iff_span_le, span_O_row_gl_mul g hg, span_k_row_gl_mul]

end GlobalTheory.PrimFrameLeft
