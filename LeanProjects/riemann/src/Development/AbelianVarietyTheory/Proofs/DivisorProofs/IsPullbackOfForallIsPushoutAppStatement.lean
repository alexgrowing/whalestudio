import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfForallIsPushoutApp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutAppLEOfIsPullbackOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchlessingerFlatFibreProductStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE : ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  first | exact @GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app | exact GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app | (intros; apply GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app <;> assumption)
