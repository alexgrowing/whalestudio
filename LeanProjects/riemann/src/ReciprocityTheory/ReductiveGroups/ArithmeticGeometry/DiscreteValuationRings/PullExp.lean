import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

abbrev gK : pullback G.hom (jK V) ⟶ G.left := pullback.fst G.hom (jK V)

def endK (f : G ⟶ G) : pullback G.hom (jK V) ⟶ pullback G.hom (jK V) :=
  pullback.map G.hom (jK V) G.hom (jK V) f.left (𝟙 _) (𝟙 _) (by simp) (by simp)

def unitK : Spec (CommRingCat.of (FractionRing V)) ⟶ pullback G.hom (jK V) :=
  pullback.lift (jK V ≫ eSec G) (𝟙 _) (by simp [eSec])

def IsPullByEnd (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (k N : ℕ) (s : U.SecK k) (s' : U.SecK (k * N)) : Prop :=
  ∃ u : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧
    LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u unitK)
      (LB.pullGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig (k * (N - 1))) (jK V)) ∧
    GeneratorPullback.SecRel U.LG.L (fun _ : Fin 1 => gK) (fun _ => ((k * N : ℕ) : ℤ)) s'
      (fun _ : Fin 1 => gK) (fun _ => (k : ℤ)) s (endK f)
      ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)] u

end ReciprocityTheory.ChartRestriction.G.DVR
