import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentKerApp
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent : ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) → Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → ∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom) := by
  first | exact @GlobalTheory.NilThicken.isNilpotent_ker_app | exact GlobalTheory.NilThicken.isNilpotent_ker_app | (intros; apply GlobalTheory.NilThicken.isNilpotent_ker_app <;> assumption)
