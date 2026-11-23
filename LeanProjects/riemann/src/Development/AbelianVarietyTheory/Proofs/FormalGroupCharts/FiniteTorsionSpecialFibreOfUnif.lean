import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FiniteTorsionAbelianGeomPoint

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_torsion_of_pullback {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) (t : Z ⟶ S')
    (r : Z ⟶ S) (hr : t ≫ f = r) (N : ℕ)
    (h : Finite {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1}) :
    Finite {x : Over.mk r ⟶ G // x ^ N = 1} := by
  subst hr
  let e := ObjPull.pushEquiv (isGrpPullback_pullback G f) (Over.mk t)
  refine Finite.of_injective (β := {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1})
    (fun x => ⟨e.symm x.1, ?_⟩) ?_
  · have hx : (show Over.mk ((Over.mk t).hom ≫ f) ⟶ G from x.1) ^ N = 1 := x.2
    rw [← map_pow, hx, map_one]
  · intro x y hxy
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val hxy))

theorem finite_torsion_special_fibre_of_unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (β : T →+* Ω), (∀ a ∈ maximalIdeal T, β a = 0) → ∀ N : ℕ, 1 ≤ N → Finite {x : Over.mk (spMap β) ⟶ G // x ^ N = 1} := by
  intro T _ _ _ G _ _ D A U Ω _ _ β hβ N hN
  let β' : T ⧸ (maximalIdeal T) ^ (0 + 1) →+* Ω :=
    Ideal.Quotient.lift _ β (fun a ha => hβ a (by simpa using ha))
  have g := U.gt 0
  have : IsCommMonObj (Out.thickObj T (maximalIdeal T) 0 G) := Functor.isCommMonObj_obj
  have h := GlobalTheory.TorusExtTorsion.finite_torsion_geomPoint _ (Out.thickObj T (maximalIdeal T) 0 G) (Out.thickObj T (maximalIdeal T) 0 D.toPre.P.A)
    D.toPre.X g.q g.i g.q_hom g.i_hom g.isKernel (Out.TLinPf.isAb_pullback _ _ D.toPre.P.isAb) Ω
    (Geo.Tor.spMap β') N hN
  refine finite_torsion_of_pullback G (Out.thick T (maximalIdeal T) 0) (Geo.Tor.spMap β') _ ?_ N h
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory
