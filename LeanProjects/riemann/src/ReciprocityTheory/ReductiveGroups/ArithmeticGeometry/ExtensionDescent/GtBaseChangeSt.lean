import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def GtBaseChangeSt : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G], E.IsGt G →
    ∃ (E' : SplitExt S') (φ : E.X ≃+ E'.X) (e : E'.B ≅ (Over.pullback f).obj E.B),
      IsMonHom e.hom ∧
      (∀ χ : E.X, ∃ w : LB.Iso ((E.O χ).L.pull (e.hom.left ≫ pullback.fst E.B.hom f))
          (E'.O (φ χ)).L, w.IsGen) ∧
      E'.IsGt ((Over.pullback f).obj G)

def CubePullSt : Prop :=
  ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen),
      (∃ c' : CubicalStr G' (m.rigLB L hL hr), m.IsPullCubical c' c) ∧
      (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric)

structure Laws3 : Prop where
  gtBaseChange : GtBaseChangeSt
  cubePull : CubePullSt

end ReciprocityTheory.ChartRestriction.G.Out
