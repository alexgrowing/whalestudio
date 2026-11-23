import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerUnitClassModPrimePow_properties : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, (∀ y, ∃ f, X.cls l n f = y) ∧ (∀ f f' : X.Kˣ, X.cls l n f = X.cls l n f' ↔ ∃ g : X.Kˣ, f = f' * g ^ (l ^ n)) ∧ (∀ f f' : X.Kˣ, X.cls l n (f * f') = X.cls l n f + X.cls l n f') ∧ X.cls l n 1 = 0 ∧ (∀ (c : ℤ_[l]) (f : X.Kˣ), c • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n c).val)) ∧ (∀ (φ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = X.cls l n (Units.map φ.toMonoidHom f)) ∧ (∀ (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x = X.cls l (n + 1) f → AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) := by
  first | exact @GlobalTheory.KZ.H3.cls_props | exact GlobalTheory.KZ.H3.cls_props | (intros; apply GlobalTheory.KZ.H3.cls_props <;> assumption)
