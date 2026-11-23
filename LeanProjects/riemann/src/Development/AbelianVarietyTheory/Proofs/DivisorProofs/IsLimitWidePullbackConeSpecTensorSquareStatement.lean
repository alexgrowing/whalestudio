import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecTensorSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  first | (exact @GlobalTheory.CechOne.isLimit_widePullback_tensor) | (exact GlobalTheory.CechOne.isLimit_widePullback_tensor) | (intros; apply GlobalTheory.CechOne.isLimit_widePullback_tensor  <;> assumption)
