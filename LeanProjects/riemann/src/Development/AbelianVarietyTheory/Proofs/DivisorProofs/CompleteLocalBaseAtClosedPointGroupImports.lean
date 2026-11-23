import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

def IsBC {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) : Prop :=
  ∃ (ev₀ : R →+* u.V) (_ : IsLocalHom ev₀) (hD : IsPullDeg ev₀ D.toPre u.D.toPre)
    (bc : u.G ≅ (Over.pullback (specOf ev₀)).obj G),
    IsMonHom bc.hom ∧ IsPullUnif ev₀ hD bc U u.U ∧ (∀ χ, hD.xe (ε χ) = χ) ∧
    (∀ r, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (ev₀ r)) = (ev r : PadicAlgCl p)) ∧
    ∃ t : u.A.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ pullback.fst _ _ = u.φ ∧
      t ≫ FinalForm.φ = genMap u.U ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) ≫ gm

end GlobalTheory.Poinc.TestAtPt
