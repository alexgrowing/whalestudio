import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericDim

theorem smoothOfRelativeDimension_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (g : ℕ), SmoothOfRelativeDimension g (pullback.snd G.hom (jK R)) → SmoothOfRelativeDimension g G.hom := by
  intro R _ _ G _ _ _ g hg
  have hdense := (ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK (V := R)).denseRange
  have hloc : ∀ x : G.left, ∃ W : G.left.Opens, x ∈ W ∧
      SmoothOfRelativeDimension g (W.ι ≫ G.hom) := by
    intro x
    obtain ⟨n, W, hxW, hW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    refine ⟨W, hxW, ?_⟩
    have hopen : IsOpen (G.hom '' (W : Set G.left)) := G.hom.isOpenMap _ W.isOpen
    obtain ⟨y, w, hwW, hwy⟩ := hdense.exists_mem_open hopen ⟨G.hom x, x, hxW, rfl⟩
    obtain ⟨z, hz, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := jK R) w y hwy
    have hzW : pullback.fst G.hom (jK R) z ∈ W := by rw [hz]; exact hwW
    have hng : n = g :=
      ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback G.hom (jK R)) hW hg z hzW
    exact hng ▸ hW
  have i1 : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension g)
  choose W hxW hW using hloc
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) hW

end GlobalTheory.GenericDim
