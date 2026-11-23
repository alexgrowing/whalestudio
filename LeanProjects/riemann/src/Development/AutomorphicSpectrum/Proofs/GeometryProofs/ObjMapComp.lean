import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_exists_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' S'' : Scheme.{0}) (s' : S' ⟶ Sp B) (s'' : S'' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (o'' : Obj D l b s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f) (m' : ObjMap o'' o' f'), ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  intro E _ _ _ H D l B _ b S s S' S'' s' s'' o o' o'' f f' m m'
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H S S' S'' o.t o'.t o''.t f f' m.toSABMap m'.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  refine ⟨{ toSABMap := n, eta := fun x => ?_, etaA := fun x => ?_ }, hn⟩
  · rw [hn', ← Category.assoc, m'.eta, Category.assoc, m.eta, Category.assoc]
  · rw [hn', ← Category.assoc, m'.etaA, Category.assoc, m.etaA, Category.assoc]

end GlobalTheory.CompanionTheory.Ar
