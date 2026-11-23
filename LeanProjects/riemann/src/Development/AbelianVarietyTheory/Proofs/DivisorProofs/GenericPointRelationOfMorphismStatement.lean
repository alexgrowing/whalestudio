import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointRelationOfMorphism
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_relation_of_morphism : ∀ (F : Type) [Field F] [CharZero F] (I I' : Type) (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop), Side Y Y' Rel → ∀ (i : I) (i' : I') (φ : (Y i).X ⟶ (Y' i').X), φ ≫ (Y' i').str = (Y i).str →
      Rel (AlgebraicClosure (Y i).Fn) i i' (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i))
        (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i) ≫ φ) →
      ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ (Y i).X), Rel K i i' p (p ≫ φ) := by
  first | exact @GlobalTheory.ShFam.GalCarry.Corr.AllPoints.rel_of_generic | exact GlobalTheory.ShFam.GalCarry.Corr.AllPoints.rel_of_generic | (intros; apply GlobalTheory.ShFam.GalCarry.Corr.AllPoints.rel_of_generic <;> assumption)
