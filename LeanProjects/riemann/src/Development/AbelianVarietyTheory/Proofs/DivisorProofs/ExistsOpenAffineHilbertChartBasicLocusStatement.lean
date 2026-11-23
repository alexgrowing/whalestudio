import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_affineHilbertChartBasic_locus : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), ∃ W : Z.Opens, (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Z), Set.range a ⊆ (W : Set Z) ↔ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map a.op y)) ∧ (CompactSpace Z → IsCompact (W : Set Z)) := by
  first | (exact @GlobalTheory.HilbAff.Locus.exists_basic_locus) | (exact GlobalTheory.HilbAff.Locus.exists_basic_locus) | (intros; apply GlobalTheory.HilbAff.Locus.exists_basic_locus  <;> assumption)
