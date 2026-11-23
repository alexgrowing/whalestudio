import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroups_neighborhood_basis : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (U : Set (GL (Fin n) L)), IsOpen U → (1 : GL (Fin n) L) ∈ U → ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε → (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.congK_cofinal | exact GlobalTheory.CompanionTheory.CartGL.congK_cofinal | (intros; apply GlobalTheory.CompanionTheory.CartGL.congK_cofinal <;> assumption)
