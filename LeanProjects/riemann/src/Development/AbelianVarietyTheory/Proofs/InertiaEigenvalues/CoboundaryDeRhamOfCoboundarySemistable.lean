import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem cocycle_dies_dR_of_dies_st : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (c : ↥(GK K) → V) (z : V ⊗[ℚ_[l]] Bst P), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b := by
  intro l _ P AI T K V _ _ ρ c z hz
  obtain ⟨ι, hC, hEq⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hst, -, hone⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hC hEq K V ρ
  refine ⟨LinearMap.lTensor V ι.toLinearMap z, fun g => ?_⟩
  rw [← hone (c g), hz g, map_sub, hst g z]

end GlobalTheory
