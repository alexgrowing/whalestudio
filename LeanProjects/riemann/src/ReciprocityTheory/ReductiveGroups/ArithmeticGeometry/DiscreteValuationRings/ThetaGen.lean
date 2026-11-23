import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def SecIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y} (a : R)
    (σ τ : LB.Sec L) : Prop :=
  ∀ j, σ.f j = resTop _ (scal p a) * τ.f j

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def SecBGenerates (k : ℕ) (α : D.toPre.X) (s : D.toPre.SecB k α) : Prop :=
  ∀ s' : D.toPre.SecB k α, ∃! a : R, SecIsMul D.toPre.P.A.hom a s' s

def IsTheta (U : Unif I D A G) (ϑ : H0 U.LG.L 1) : Prop :=
  ∀ e : ℕ, ∃ f : ∀ α : D.toPre.X, D.toPre.SecB 1 α, U.ExpandsAt e 1 ϑ f ∧ SecBGenerates 1 0 (f 0)

def NonzeroOnSpecial (U : Unif I D A G) (σ : H0 U.LG.L 1) : Prop :=
  ∃ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom (σ.f j) ≠ 0

end ReciprocityTheory.ChartRestriction.G.DVR

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

end ReciprocityTheory.ChartRestriction.G.DVR
