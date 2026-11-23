import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw

def IsRigPull {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B']
    [GrpObj B] [IsCommMonObj B] (p : S' ⟶ S) (F : B'.left ⟶ B.left) (L' : RigLB B') (L : RigLB B) : Prop :=
  ∃ he : eSec B' ≫ F = (show (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left from p) ≫ eSec B,
  ∃ w : LB.Iso L'.L (L.L.pull F), w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec B') (fun _ => 1)) L'.rig
      (rigPullOf F p he L.L L.rig)

def Identifies {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (E' : SplitExt S')
    (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X) : Prop :=
  haveI := E.isAbelian.comm
  haveI := E'.isAbelian.comm
  IsMonHom φ.hom ∧
    ∀ χ : E'.X, IsRigPull p (φ.hom.left ≫ pullback.fst E.B.hom p) (E'.O χ) (E.O (ψ χ))

def IsBaseChange {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (E' : SplitExt S') : Prop :=
  ∃ (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X), Identifies p E E' φ ψ

def GtBaseChangeLaw : Prop :=
  ∀ {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G],
    E.IsGt G → ∃ E' : SplitExt S', IsBaseChange p E E' ∧ E'.IsGt ((Over.pullback p).obj G)

def CubicalPullLaw : Prop :=
  ∀ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen)
      (c' : CubicalStr G' (m.rigLB L hL hr)),
      c'.t = m.thetaPull L.L c.t ∧ m.IsPullCubical c' c ∧
        (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric)

def Laws : Prop := GtBaseChangeLaw ∧ CubicalPullLaw

def GtPresentationBaseChangeLaw : Prop :=
  ∀ {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (D : E.GtDatum G),
    ∃ (E' : SplitExt S') (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X)
      (D' : E'.GtDatum ((Over.pullback p).obj G))
      (τ : (splitTorus S' E'.X).left ⟶ (splitTorus S E.X).left),
      Identifies p E E' φ ψ ∧
      D'.q ≫ φ.hom = (Over.pullback p).map D.q ∧
      τ ≫ (splitTorus S E.X).hom = (splitTorus S' E'.X).hom ≫ p ∧
      (∀ χ : E'.X, Units.map τ.appTop.hom.toMonoidHom (charUnit S E.X (ψ χ)) =
        charUnit S' E'.X χ) ∧
      D'.i.left ≫ pullback.fst G.hom p = τ ≫ D.i.left

theorem CubicalPullLaw.ofHom (h : CubicalPullLaw) : CubicalPullOfHomSt.{0} := by
  intro S G' G _ _ _ _ f _ L c
  obtain ⟨hL, hr, c', hc, _⟩ := h (CubeMap.ofHom f) L c
  exact ⟨hL, hr, c', hc⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw

end
