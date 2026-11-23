import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues : ∀ (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → GlobalTheory.LGrp.IsIrrSmooth π → IsSmooth ρ → ∀ x ∈ fixed π K, x ≠ 0 → ∀ y ∈ fixed ρ K, y ≠ 0 → (∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) → GlobalTheory.LGrp.IsSubquot π ρ := by
  first | exact @GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | exact GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | (intros; apply GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues <;> assumption)
