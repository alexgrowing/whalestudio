import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SideGenericPointLift
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_generic_point_lift : ∀ (F : Type) [Field F] [CharZero F] (I I' : Type) (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop), Side Y Y' Rel → ∀ i : I, ∃ (i' : I') (p' : Sp (Y i).Fn ⟶ (Y' i').X),
      p' ≫ (Y' i').str = genericPt (Y i) ≫ (Y i).str ∧
      Rel (AlgebraicClosure (Y i).Fn) i i' (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i))
        (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ p') := by
  first | exact @GlobalTheory.ShFam.GalCarry.Corr.partner_generic_descends | exact GlobalTheory.ShFam.GalCarry.Corr.partner_generic_descends | (intros; apply GlobalTheory.ShFam.GalCarry.Corr.partner_generic_descends <;> assumption)
