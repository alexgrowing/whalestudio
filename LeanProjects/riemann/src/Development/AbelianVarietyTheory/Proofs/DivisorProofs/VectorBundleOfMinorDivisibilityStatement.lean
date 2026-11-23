import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfMinorDivisibility
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_of_minor_divisibility : ∀ (Y : Scheme.{0}) [IsIntegral Y] (F E : Y.Modules) (φ : F ⟶ E) (r m : ℕ), (∀ y : Y, ∃ (V : Y.Opens) (eF : Fin m → Γ(F, V)) (eE : Fin r → Γ(E, V)) (a : Matrix (Fin r) (Fin m) Γ(Y, V)) (J : Fin r → Fin m), y ∈ V ∧ GlobalTheory.VB.IsFrame eF ∧ GlobalTheory.VB.IsFrame eE ∧ (∀ j, φ.app V (eF j) = ∑ k, a k j • eE k) ∧ (a.submatrix id J).det ≠ 0 ∧ ∀ K : Fin r → Fin m, (a.submatrix id J).det ∣ (a.submatrix id K).det) → GlobalTheory.VB.IsVB (Limits.image φ) r := by
  first | exact @GlobalTheory.ImgVB.isVB_image_of_minor | exact GlobalTheory.ImgVB.isVB_image_of_minor | (intros; apply GlobalTheory.ImgVB.isVB_image_of_minor <;> assumption)
