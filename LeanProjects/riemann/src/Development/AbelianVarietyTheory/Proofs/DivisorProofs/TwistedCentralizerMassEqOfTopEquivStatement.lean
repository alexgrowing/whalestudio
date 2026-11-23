import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G') (δ : G) (δ' : G'), IsClosed (twCent θ δ : Set G) → IsClosed (twCent θ' δ' : Set G') → ∀ (e : twCent θ δ ≃ₜ* twCent θ' δ'), (∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') → mass θ Γ δ = mass θ' Γ' δ' := by
  first | exact @GlobalTheory.MassTor.mass_eq_of_equiv | exact GlobalTheory.MassTor.mass_eq_of_equiv | (intros; apply GlobalTheory.MassTor.mass_eq_of_equiv <;> assumption)
