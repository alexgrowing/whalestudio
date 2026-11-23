import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimZeroStalkTrivialPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dim_zero_stalk_trivial_period : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Z.X) (tW : SAB H (Sp W)) (_ : SABMap tW Z.t χ) (PW : PELUnif (maximalIdeal W) tW), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) ≤ 0 → Subsingleton PW.D.toPre.X := by
  first | exact @GlobalTheory.TraitGeneric.subsingleton_of_closed_dim_zero | exact GlobalTheory.TraitGeneric.subsingleton_of_closed_dim_zero | (intros; apply GlobalTheory.TraitGeneric.subsingleton_of_closed_dim_zero <;> assumption)
