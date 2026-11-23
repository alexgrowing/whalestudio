import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeComapOfExactFlat
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_comap_of_exact_flat : ∀ (A E : Type) [CommRing A] [CommRing E] [Algebra A E] [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂] [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂] (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂), Function.Injective j → Function.Exact j q → Function.Surjective q → IsBaseChange E N₁.subtype → IsBaseChange E N₂.subtype → (∀ x ∈ N₁, q x ∈ N₂) → IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  first | exact @GlobalTheory.isBaseChange_comap_of_exact | exact GlobalTheory.isBaseChange_comap_of_exact | (intros; apply GlobalTheory.isBaseChange_comap_of_exact <;> assumption)
