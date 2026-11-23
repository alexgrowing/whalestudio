import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal

namespace GlobalTheory.LatModel

def IsPlaceOver (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ)
    (R : Subring ℂ) : Prop :=
  IsDiscreteValuationRing R ∧ (∀ x ∈ R, Sz l lam 0 x) ∧ ∀ x ∈ k, Sz l lam 0 x → x ∈ R

def Eventually (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (P : Subring ℂ → Prop) : Prop :=
  ∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ ∀ R, IsPlaceOver l lam k R → P R

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem IsPlaceOver.mono {k k' : IntermediateField ℚ ℂ} {R : Subring ℂ} (h : k ≤ k')
    (hR : IsPlaceOver l lam k' R) : IsPlaceOver l lam k R :=
  ⟨hR.1, hR.2.1, fun x hx hs ↦ hR.2.2 x (h hx) hs⟩

theorem Eventually.and {P Q : Subring ℂ → Prop} (h₁ : Eventually l lam P) (h₂ : Eventually l lam Q) :
    Eventually l lam fun R ↦ P R ∧ Q R := by
  obtain ⟨k, hk, H⟩ := h₁
  obtain ⟨k', hk', H'⟩ := h₂
  exact ⟨k ⊔ k', inferInstance, fun R hR ↦ ⟨H R (hR.mono le_sup_left), H' R (hR.mono le_sup_right)⟩⟩

theorem Eventually.mono {P Q : Subring ℂ → Prop} (h : Eventually l lam P) (hPQ : ∀ R, P R → Q R) :
    Eventually l lam Q := by
  obtain ⟨k, hk, H⟩ := h
  exact ⟨k, hk, fun R hR ↦ hPQ R (H R hR)⟩

theorem eventually_of_forall {P : Subring ℂ → Prop} (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    (h : ∀ R, IsPlaceOver l lam k R → P R) : Eventually l lam P :=
  ⟨k, inferInstance, h⟩

end GlobalTheory.LatModel
