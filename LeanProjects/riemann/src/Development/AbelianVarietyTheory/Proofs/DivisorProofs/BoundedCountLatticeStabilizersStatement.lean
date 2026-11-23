import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCountLatticeStabilizers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_count_lattice_stabilizers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L],
    ∃ c : ℕ, ∀ m : ℕ, 0 < m → ∃ T : Finset (GAd σ J), T.card ≤ m ^ c ∧ ∀ g : GAd σ J,
      (∀ v, ∀ y ∈ latLoc F L v, m • ((matHom (Fv F v) σ J (proj σ J v g)).1 *ᵥ y) ∈ latLoc F L v ∧
        m • ((matHom (Fv F v) σ J (proj σ J v g)⁻¹).1 *ᵥ y) ∈ latLoc F L v) →
      ∃ x ∈ T, ∀ v, (proj σ J v x)⁻¹ * proj σ J v g ∈ stabLoc σ J L v := by
  first | exact @GlobalTheory.StabClassCount.exists_card_le | exact GlobalTheory.StabClassCount.exists_card_le | (intros; apply GlobalTheory.StabClassCount.exists_card_le <;> assumption)
