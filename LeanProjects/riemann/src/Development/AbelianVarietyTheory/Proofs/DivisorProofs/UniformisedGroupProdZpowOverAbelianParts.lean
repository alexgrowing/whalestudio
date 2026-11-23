import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem over₀_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a b h e
  let P := Over.pullback (thick R I e)
  have := (U₀.gt e).q_hom
  let fG : (G ⟶ G₀) →* (P.obj G ⟶ P.obj G₀) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  let fB : (D.toPre.P.A ⟶ D₀.toPre.P.A) →* (P.obj D.toPre.P.A ⟶ P.obj D₀.toPre.P.A) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  have hG : P.map (∏ i, a i ^ n i) = ∏ i, P.map (a i) ^ n i :=
    (map_prod fG _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fG _ _)
  have hB : P.map (∏ i, b i ^ n i) = ∏ i, P.map (b i) ^ n i :=
    (map_prod fB _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fB _ _)
  show P.map (∏ i, a i ^ n i) ≫ (U₀.gt e).q = (U.gt e).q ≫ P.map (∏ i, b i ^ n i)
  rw [hG, hB, prod_zpow_comp, comp_prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [h i e]

end GlobalTheory.Mum.PowData
