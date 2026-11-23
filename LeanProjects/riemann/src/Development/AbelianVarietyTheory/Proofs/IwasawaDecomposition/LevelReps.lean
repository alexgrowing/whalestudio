import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ArcExt

open MonoidalCategory CartesianMonoidalCategory

def LevelRep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (y : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (m : SABMap t Y.t y)
    (P : PELUnif (maximalIdeal V) t) (k : ℕ) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Prop :=
  ∃ r : Out.QkPt P.D.toPre (FractionRing V) k,
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (yF : Sp F ⟶ Xo.XF c),
      yF ≫ Y.j = Out.jFK (R := V) F ≫ Out.jK V ≫ y →
      ∀ (q : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := V) F ⟶ P.A.A), QkExt (algebraMap _ F) r q →
        x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK V) ≫ m.φ = yF ≫ σ.left ≫ Y.m.φ →
        P.ToA F k q x

def LevelReps {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (y : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (m : SABMap t Y.t y)
    (P : PELUnif (maximalIdeal V) t) : Prop :=
  (∀ v, LevelRep Y y t m P l.A (Y.oF.etaA v)) ∧
    ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), LevelRep Y y t m P l.M (Y.oF.eta v)

end GlobalTheory.ArcExt
