import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormResidueFieldData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_form_residue_field_data : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q : ℕ) (τ : Res S ϖ →+* Res S ϖ), GoodRing S σ ϖ q → GoodForm S σ H → (∀ a ∈ S, τ (red S ϖ a) = red S ϖ (σ a)) → ∃ k : Subring (Res S ϖ), ∃ w : Res S ϖ, ∃ H' : Matrix n n (Res S ϖ), (∀ x ∈ k, τ x = x) ∧ w + τ w = 1 ∧ IsUnit (w - τ w) ∧ (∀ x : Res S ϖ, ∃ a ∈ k, ∃ b ∈ k, x = a + b * w) ∧ (∀ x ∈ k, x ≠ 0 → ∃ y ∈ k, x * y = 1) ∧ Nat.card k = q ∧ Formalism.UG.cT τ (H.map (red S ϖ)) = H.map (red S ϖ) ∧ H.map (red S ϖ) * H' = 1 := by
  first | exact @GlobalTheory.ResGlue.resGlue | exact GlobalTheory.ResGlue.resGlue | (intros; apply GlobalTheory.ResGlue.resGlue <;> assumption)
