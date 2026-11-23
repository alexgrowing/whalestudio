import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def UT (N : Near π G) : Over (pullback π π) := Over.mk (pullback.snd N.U.hom (pullback.fst π π ≫ π))

def toS (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback N.U.hom π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
    rw [Category.assoc, hp]; exact pullback.condition)

def embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback G.hom p :=
  pullback.lift (toS N p hp ≫ N.u) (pullback.snd _ _) (by
    rw [Category.assoc, N.u_over, toS, pullback.lift_snd])

def emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⟶ (Over.pullback p).obj G :=
  Over.homMk (embL N p hp) (pullback.lift_snd _ _ _)

def sum [GrpObj G] (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⊗ UT N ⟶ (Over.pullback p).obj G :=
  (fst (UT N) (UT N) ≫ emb N p hp) * (snd (UT N) (UT N) ≫ emb N p hp)

end GlobalTheory.Mum.Desc
