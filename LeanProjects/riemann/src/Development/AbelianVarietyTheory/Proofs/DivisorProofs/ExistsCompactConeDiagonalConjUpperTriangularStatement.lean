import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactConeDiagonalConjUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  first | exact @GlobalTheory.upperCone_conj_compact | exact GlobalTheory.upperCone_conj_compact | (intros; apply GlobalTheory.upperCone_conj_compact <;> assumption)
