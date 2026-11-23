import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqTan
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Bridge

variable {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

abbrev GS : Over (Spec (CommRingCat.of S)) := (Over.pullback x0).obj G

instance : GrpObj (GS G x0) := Functor.grpObjObj

def br {A : Type} [CommRing A] [Algebra S A] (f : overAt x0 A ⟶ G) : sp (R₀ := S) A ⟶ GS G x0 :=
  (Over.mapPullbackAdj x0).homEquiv (sp (R₀ := S) A) G f

variable {G x0}

theorem br_injective {A : Type} [CommRing A] [Algebra S A] : Function.Injective (br G x0 (A := A)) := by
  intro f g h
  exact ((Over.mapPullbackAdj x0).homEquiv _ _).injective h

theorem br_mul {A : Type} [CommRing A] [Algebra S A] (f g : overAt x0 A ⟶ G) :
    br G x0 (f * g) = br G x0 f * br G x0 g := by
  simp only [br, Adjunction.homEquiv_unit]
  first
  | rw [Functor.map_mul, comp_mul]
  | rw [Functor.map_mul, Hom.comp_mul]
  | rw [Functor.map_mul, MonObj.comp_mul]
  | rw [Functor.map_mul, Mon_Class.comp_mul]

theorem br_one {A : Type} [CommRing A] [Algebra S A] : br G x0 (1 : overAt x0 A ⟶ G) = 1 := by
  simp [br, Adjunction.homEquiv_unit]

theorem homAt_eq {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (ψ : A →ₐ[S] B) :
    homAt x0 ψ = (Over.map x0).map (spMap ψ) := by
  first
  | rfl
  | exact Over.OverMorphism.ext rfl

theorem br_comp {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (ψ : A →ₐ[S] B)
    (f : overAt x0 A ⟶ G) : br G x0 (homAt x0 ψ ≫ f) = spMap ψ ≫ br G x0 f := by
  unfold br
  rw [homAt_eq, Adjunction.homEquiv_naturality_left]

end Bridge

theorem expUniqLoc : ExpUniqLocSt := by
  intro E _ _ _ H Dw l Xo S _ _ _ x0 d x x' hx hx' ht
  haveI : IsCommMonObj Xo.univ.t.G := Xo.univ.t.semi.comm
  haveI : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  haveI : Smooth (GS Xo.univ.t.G x0).hom := by
    show Smooth (pullback.snd Xo.univ.t.G.hom x0)
    infer_instance
  obtain ⟨n, xu, hxu⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (GS Xo.univ.t.G x0)
  have key : ∀ m, br Xo.univ.t.G x0 (x' m * (x m)⁻¹) = 1 := by
    refine trivT hxu (fun m => br Xo.univ.t.G x0 (x' m * (x m)⁻¹)) ?_ ?_ ?_
    · intro m
      rw [← br_comp]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv, hx.1 m, hx'.1 m]
    · intro m
      rw [← br_comp, ← br_comp, ← br_comp, ← br_mul]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv]
      rw [hx.2 m, hx'.2 m, _root_.mul_inv, _root_.mul_mul_mul_comm]
    · intro j
      rw [← br_comp, ← br_one (A := DualNumber S)]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv, ht j, _root_.mul_inv_cancel]
  funext m
  have h := key m
  rw [← br_one] at h
  exact (_root_.mul_inv_eq_one.1 (br_injective h)).symm

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
