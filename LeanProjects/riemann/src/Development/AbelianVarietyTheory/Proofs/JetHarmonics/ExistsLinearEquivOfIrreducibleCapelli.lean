import Mathlib
import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleIsHW

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem exists_linearEquiv_of_irreducible_capelli :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [AddCommGroup V₂]
      [Module ℂ V₂] [FiniteDimensional ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
      (E₂ : Fin n → Fin n → Module.End ℂ V₂) (m : Fin n → ℂ), GlRel E₁ → GlRel E₂ → Irr E₁ → Irr E₂ →
      (∀ w v, qdet E₁ w v = cpol m w • v) → (∀ w v, qdet E₂ w v = cpol m w • v) →
      ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ _ V₂ _ _ _ n E₁ E₂ m g₁ g₂ i₁ i₂ c₁ c₂
  haveI := i₁.1
  haveI := i₂.1
  obtain ⟨ν₁, v₁, -, hv₁, hw₁, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₁ n E₁ g₁ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  obtain ⟨ν₂, v₂, -, hv₂, hw₂, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₂ n E₂ g₂ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have p₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₁ (mem_CapSp.2 fun w => c₁ w v₁) hv₁ hw₁
  have p₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₂ (mem_CapSp.2 fun w => c₂ w v₂) hv₂ hw₂
  have s₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₁ n E₁ ν₁ v₁ g₁ hw₁ hv₁)
  have s₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₂ n E₂ ν₂ v₂ g₂ hw₂ hv₂)
  have h := (Formalism.FourierDecayAlt.P.separating_polynomials n _ _ (fun w => (p₁ w).symm.trans (p₂ w)) s₂).2 s₁
  have hν : ν₁ = ν₂ := by
    funext j
    exact sub_left_injective (congrFun h j)
  subst hν
  exact exists_linearEquiv_of_irreducible_isHW V₁ V₂ n E₁ E₂ ν₁ v₁ v₂ g₁ g₂ i₁.2 i₂.2 hw₁ hw₂ hv₁ hv₂

end GlobalTheory
