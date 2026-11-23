import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleOfSemistableCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActVdRMemTensorDeRhamFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyFrobeniusSolutionFilStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqTmulOneOfMonodromyFrobeniusFiltrationStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem GlobalTheory.semistable_class_of_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ x hx y hy hxy
  obtain ⟨ι, hιC, hιact⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hιst, -, -⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hιC hιact K V ρ
  obtain ⟨z, hNz, hφz, hFz⟩ := GlobalTheory.T.exists_monodromy_frobenius_solution_fil l P AI T ι hιC K V x y hxy
  have hx' := (mem_Dst P ρ).mp hx
  have hy' := (mem_Dst P ρ).mp hy
  have hw : ∀ g : ↥(GK K), ∃ v : V, stRep P ρ g z - z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
    intro g
    refine GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration l P AI T ι hιC K V (stRep P ρ g z - z) ?_ ?_ ?_
    · rw [map_sub, ← Module.End.mul_apply, monV_stRep, Module.End.mul_apply, hNz, hx', sub_self]
    · have hφz' : phiV P ℚ_[l] V z = z + y := by rw [← hφz]; abel
      rw [map_sub, ← Module.End.mul_apply, phiV_stRep, Module.End.mul_apply, hφz', map_add, hy']
      abel
    · rw [map_sub, hιst]
      exact Submodule.sub_mem _ (GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration l P K V ρ 0 g _ hFz) hFz
  choose c hc using hw
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := fun g => (hc g).symm
  exact ⟨z, c, GlobalTheory.T.continuousCocycle_of_semistable_coboundary l P AI T K V ρ hρ z c hc', hc', hNz⟩
