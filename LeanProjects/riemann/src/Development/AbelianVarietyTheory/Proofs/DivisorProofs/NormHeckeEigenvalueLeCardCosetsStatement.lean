import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosets
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets : ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) → (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) → {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x → ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  first | exact @GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul | exact GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul | (intros; apply GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul <;> assumption)
