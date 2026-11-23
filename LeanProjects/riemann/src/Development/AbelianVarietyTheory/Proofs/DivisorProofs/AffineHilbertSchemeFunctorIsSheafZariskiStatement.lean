import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeFunctorIsSheafZariski
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ), Presieve.IsSheaf Scheme.zariskiTopology (GlobalTheory.HilbAff.functor A B r) := by
  first | (exact @GlobalTheory.HilbAff.isSheaf_functor) | (exact GlobalTheory.HilbAff.isSheaf_functor) | (intros; apply GlobalTheory.HilbAff.isSheaf_functor <;> assumption)
