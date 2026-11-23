import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem valuative_lift_of_isProper {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s] (y : Sp K ⟶ X) (r : Sp V ⟶ S)
    (h : y ≫ s = spMap (algebraMap V K) ≫ r) :
    ∃ x : Sp V ⟶ X, spMap (algebraMap V K) ≫ x = y ∧ x ≫ s = r := by
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := K, i₁ := y, i₂ := r, commSq := ⟨h⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem range_subset_abLocus_of_isProper {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f)
    [IsProper G'.hom] : Set.range f ⊆ abLocus G := by
  rintro _ ⟨x, rfl⟩
  refine (abLocus_pullback abLocusOne hG h x).2 ?_
  intro K _ _ t _
  infer_instance

theorem model_point_extends :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
  (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  (b : O →+* V) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j ≫ Y.s = spMap (algebraMap V K) ≫ spMap b →
  ∃ (y' : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (_ : SABMap t Y.t y'), y' ≫ Y.s = spMap b ∧ spMap (algebraMap V K) ≫ y' = y ≫ Y.j ∧
    (IsAbelianScheme t.G → Set.range y' ⊆ abLocus Y.t.G) := by
  intro E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ b y hy
  have := projProper O Y.X Y.s Y.proj
  obtain ⟨y', h₁, h₂⟩ := valuative_lift_of_isProper Y.s (y ≫ Y.j) (spMap b) (by rw [Category.assoc, hy])
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull y' Y.t
  refine ⟨y', _, m, h₂, h₁, fun hA => ?_⟩
  have := hA.proper
  exact range_subset_abLocus_of_isProper Y.t.semi m.cart.1

end GlobalTheory
