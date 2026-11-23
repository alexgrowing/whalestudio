import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFree
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_representable_finite_free : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  first | exact @GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | exact GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | (intros; apply GlobalTheory.TorsionRep.exists_finite_free_torsion_rep <;> assumption)
