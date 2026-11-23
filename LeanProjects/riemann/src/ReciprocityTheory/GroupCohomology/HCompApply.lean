import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.FiberFirstH0Injective
import ReciprocityTheory.GroupCohomology.ProdHolds
import ReciprocityTheory.GroupCohomology.EqZeroOfLe

namespace ReciprocityTheory.Coh.SelH

open ReciprocityTheory.Coh Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R]

def piHom {ι : Type u} {A B : ι → Cx R} (f : ∀ v, Hom (A v) (B v)) : Hom (pi A) (pi B) where
  f n := LinearMap.pi fun v => ((f v).f n).comp (LinearMap.proj v)
  comm n x := funext fun v => (f v).comm n (x v)

def negHom {A B : Cx R} (φ : Hom A B) : Hom A B where
  f n := -(φ.f n)
  comm n x := by simp [φ.comm]

def inr (A B : Cx R) : Hom B (prod A B) where
  f _ := LinearMap.inr R _ _
  comm n _ := Prod.ext (map_zero (A.d n)).symm rfl

end

end ReciprocityTheory.Coh.SelH
