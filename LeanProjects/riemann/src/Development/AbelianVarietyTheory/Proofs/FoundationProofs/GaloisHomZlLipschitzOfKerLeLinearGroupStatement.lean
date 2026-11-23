import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisHomZlLipschitzOfKerLeLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisHom_zl_lipschitz_of_ker_le_linearGroup : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → Continuous lam → r.ker ≤ lam.ker → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) → ‖(lam g).toAdd‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ m‖ := by
  first | exact @GlobalTheory.Ord2.hom_lipschitz_of_ker_le | exact GlobalTheory.Ord2.hom_lipschitz_of_ker_le | (intros; apply GlobalTheory.Ord2.hom_lipschitz_of_ker_le <;> assumption)
