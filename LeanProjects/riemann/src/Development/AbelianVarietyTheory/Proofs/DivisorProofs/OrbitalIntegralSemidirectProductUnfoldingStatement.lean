import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding : ∀ (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace P] [TopologicalSpace M] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ γ : M, (∀ p, p ∈ twCent (MonoidHom.id P) (s γ) ↔ ∃ t ∈ twCent (MonoidHom.id M) γ, s t = p) → (∀ p, p ∈ cptPart (twCent (MonoidHom.id P) (s γ)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id M) γ), s t = p) → (∀ q : M, twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id M) γ)) → (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → {d : DoubleCoset.Quotient (twCent (MonoidHom.id P) (s γ) : Set P) (KP : Set P) | F ((Quotient.out d)⁻¹ * s γ * Quotient.out d) ≠ 0}.Finite → twOrb (MonoidHom.id P) KP (s γ) F = twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) := by
  first | exact @GlobalTheory.Unfold.twOrb_unfold | exact GlobalTheory.Unfold.twOrb_unfold | (intros; apply GlobalTheory.Unfold.twOrb_unfold <;> assumption)
