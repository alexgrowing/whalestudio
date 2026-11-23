import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.EdgeNoTrunc
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EChain

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

namespace ShapeDiagramLemmas

theorem shape_al (μ : YoungDiagram) :
    (univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)).card = μ.rowLen 0 - μ.rowLen 1 := by
  have h : ∀ c : Fin (μ.rowLen 0), μ.colLen c = 1 ↔ μ.rowLen 1 ≤ c.val := by
    intro c
    have h0 : 0 < μ.colLen c :=
      YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 c.isLt)
    have h1 : (1 < μ.colLen c) ↔ c.val < μ.rowLen 1 := by
      rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    omega
  simp_rw [h]
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun c => if μ.rowLen 1 ≤ c then 1 else 0),
    ← Finset.card_filter]
  have : (range (μ.rowLen 0)).filter (fun c => μ.rowLen 1 ≤ c) = Ico (μ.rowLen 1) (μ.rowLen 0) := by
    ext; simp [and_comm]
  rw [this, Nat.card_Ico]

theorem shape {ν : ℕ} (TT : Finset (ZMod (2 * ν))) (μ : ZMod (2 * ν) → YoungDiagram)
    (s : ZMod (2 * ν)) :
    alG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 0 - (μ s).rowLen 1 else 0) ∧
    capG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 1 else (μ s).rowLen 0) := by
  have h1 : (μ s).rowLen 1 ≤ (μ s).rowLen 0 := (μ s).rowLen_anti 0 1 (by omega)
  unfold capG alG
  split_ifs
  · rw [shape_al]; exact ⟨rfl, by dsimp only; omega⟩
  · exact ⟨rfl, rfl⟩

end ShapeDiagramLemmas

end Formalism.InvariantFactorPaths.G7
