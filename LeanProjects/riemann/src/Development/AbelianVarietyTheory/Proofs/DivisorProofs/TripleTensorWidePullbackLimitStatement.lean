import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTensorWidePullbackLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_tensor_wide_pullback_limit : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (2 + 1) => GlobalTheory.CechOne.fB A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B))))) (GlobalTheory.CechOne.y2 A B) (GlobalTheory.CechOne.hy2 A B))) := by
  first | (exact @GlobalTheory.CechOne.spec_tensor3_isLimit) | (exact GlobalTheory.CechOne.spec_tensor3_isLimit) | (intros; apply GlobalTheory.CechOne.spec_tensor3_isLimit  <;> assumption)
