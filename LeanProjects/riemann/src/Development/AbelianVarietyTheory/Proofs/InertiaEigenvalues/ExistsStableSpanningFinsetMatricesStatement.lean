import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableSpanningFinsetMatrices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_spanning_finset_matrices : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (Om l)) (L : FinExt l), Continuous ρ → (∀ g i j, (ρ g).val i j ∈ L.1) → ∃ t : Finset (Matrix (Fin a) (Fin a) (Om l)), (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧ (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧ (∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c y) • y = 1) ∧ ∀ g, ∀ x ∈ t, ∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], (ρ g).val * x = ∑ y ∈ t, zOm l (c y) • y := by
  first | exact @GlobalTheory.exists_stable_spanning_finset | exact GlobalTheory.exists_stable_spanning_finset | (intros; apply GlobalTheory.exists_stable_spanning_finset; all_goals assumption)
