import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SideGenericPointRelation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_generic_point_relation : ∀ (F : Type) [Field F] [CharZero F] (I I' : Type) (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop), Side Y Y' Rel → ∀ (i : I) (i' : I') (p' : Sp (Y i).Fn ⟶ (Y' i').X),
      Rel (AlgebraicClosure (Y i).Fn) i i' (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i))
        (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ p') →
      ∀ (y : (Y i).X) (W₁ W₂ : ValuationSubring (Y i).Fn) (q₁ : Sp W₁ ⟶ (Y' i').X) (q₂ : Sp W₂ ⟶ (Y' i').X),
        GlobalTheory.DominatesStalk W₁ y → GlobalTheory.DominatesStalk W₂ y → spMap (algebraMap W₁ (Y i).Fn) ≫ q₁ = p' →
        spMap (algebraMap W₂ (Y i).Fn) ≫ q₂ = p' → q₁ (IsLocalRing.closedPoint W₁) = q₂ (IsLocalRing.closedPoint W₂) := by
  first | exact @GlobalTheory.ShFam.GalCarry.Corr.centre_eq_of_dominatesStalk | exact GlobalTheory.ShFam.GalCarry.Corr.centre_eq_of_dominatesStalk | (intros; apply GlobalTheory.ShFam.GalCarry.Corr.centre_eq_of_dominatesStalk <;> assumption)
