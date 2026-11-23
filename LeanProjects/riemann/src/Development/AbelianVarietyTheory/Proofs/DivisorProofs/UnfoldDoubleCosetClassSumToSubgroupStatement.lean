import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_doubleCoset_classSum_to_subgroup : ∀ {G H : Type} [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h, ι h = g) → ∀ (T : Subgroup H) (Γ' : Subgroup G), (∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g) → ∀ (K : Subgroup G) (u : G → ℂ), (∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g) → Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)) → (∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) → ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) = ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) := by
  first | exact @GlobalTheory.ClassSumUnfold.unfold_classSum | exact GlobalTheory.ClassSumUnfold.unfold_classSum | (intros; apply GlobalTheory.ClassSumUnfold.unfold_classSum <;> assumption)
