import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' : Scheme.{0}) (s' : S' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (f : S' ⟶ S) (m : ObjMap o' o f) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) (h' : TwOK o' g a), ∃ n : ObjMap (twistObj o' g a h') (twistObj o g a h) f, n.toSABMap = twistMap m.toSABMap g  := by
  intro E _ _ _ H D l B _ b S s S' s' o o' f m g a h h'
  exact ⟨{ toSABMap := twistMap m.toSABMap g
           eta := fun x => m.eta (a.a l.M x)
           etaA := fun x => m.etaA (a.a l.A x) }, rfl⟩

end GlobalTheory.CompanionTheory.Ar
