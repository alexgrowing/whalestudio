import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem isHgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ H hH
  refine ⟨fun κ hκ g => ?_, fun e => ?_⟩
  · have hK : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ KO k (A ⊕ D) :=
      (mem_parahoric.1 (GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (one_mem _) hκ)).1
    have e1 : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * g) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) * emb₂ k (Equiv.refl (A ⊕ D)) (1, g) := by
      rw [← map_mul]; simp
    have e2 : emb₂ k (Equiv.refl (A ⊕ D)) (1, g * κ) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, g) * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) := by
      rw [← map_mul]; simp
    exact ⟨by simp only [e1]; exact (hH.1 _ hK _).1, by simp only [e2]; exact (hH.1 _ hK _).2⟩
  · show H (emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e)) = _
    rw [GlobalTheory.ChainStepSupp.emb₂_one_torusElt, mtor, hH.2]
    congr 2
    simp [sumAbs, Fintype.sum_sum_type]

end GlobalTheory.ParHecke
