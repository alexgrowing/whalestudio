import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittExistsEquivOfCharpolyEqHypotheses
import Mathlib
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.brauerNesbitt_exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V) (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation → (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) → ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  first | exact @GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | exact GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | (intros; apply GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' <;> assumption)
