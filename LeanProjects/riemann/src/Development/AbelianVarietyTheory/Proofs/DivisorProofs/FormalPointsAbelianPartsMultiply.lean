import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.FormalMul

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem map_b_eq {U : UnifPre I D A G} {T : Over (Sp R)} {x : T ⟶ G} {g : GtPt D.toPre T}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U x g) (e : ℕ) :
    (Over.pullback (thick R I e)).map g.b = (Over.pullback (thick R I e)).map x ≫ (U.gt e).q :=
  (GlobalTheory.FormalExt.map_eq_iff I e g.b _).2 ((hg e).1.trans (Category.assoc _ _ _).symm)

theorem b_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (h h' : (𝟙_ (Over (Sp V))) ⟶ G) (g g' g'' : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h' g' → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre (h * h') g'' → g''.b = g.b * g'.b := by
  intro V _ _ _ hV D A G _ _ _ U h h' g g' g'' hg hg' hg''
  have := hV.1
  have := hV.2.2.1
  have := D.toPre.P.isAb.proper
  have h1 : Smooth (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := inferInstanceAs (Smooth (𝟙 _))
  have h1' : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of V)))).hom :=
    inferInstanceAs (GeometricallyConnected (𝟙 _))
  refine GlobalTheory.FormalExt.hom_ext_thick (maximalIdeal V) (IsAdicComplete.le_jacobson_bot _) _ fun e => ?_
  have := (U.gt e).q_hom
  rw [Functor.map_mul, map_b_eq hg, map_b_eq hg', map_b_eq hg'', Functor.map_mul, MonObj.mul_comp]

end GlobalTheory.Poinc.Sep.FormalMul
