import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutative
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_regroup_commutative : ∀ (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → C ≤ T → (∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) → (∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) → ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by
  first | exact @GlobalTheory.finsum_doubleCoset_regroup | exact GlobalTheory.finsum_doubleCoset_regroup | (intros; apply GlobalTheory.finsum_doubleCoset_regroup <;> assumption)
