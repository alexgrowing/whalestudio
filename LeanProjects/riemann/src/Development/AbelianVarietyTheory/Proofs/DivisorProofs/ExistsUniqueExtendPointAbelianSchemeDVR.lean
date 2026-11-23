import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DVRExt

theorem exists_unique_extend : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  intro R _ P W L _ _ _ _ _ _ f x
  haveI : ValuationRing W := inferInstance
  have hv : ValuativeCriterion P.A.hom := by
    have h : IsProper P.A.hom := P.isAb.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x.left ≫ P.A.hom = spMap (algebraMap W L) ≫ spMap f := by
    rw [Over.w x]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let S : ValuativeCommSq P.A.hom :=
    { R := W, K := L, i₁ := x.left, i₂ := spMap f, commSq := ⟨hsq⟩ }
  have hU := (hv S).some
  refine ⟨Over.homMk hU.default.l hU.default.fac_right, hU.default.fac_left, ?_⟩
  intro y hy
  have hy2 : y.left ≫ P.A.hom = spMap f := Over.w y
  let T : S.commSq.LiftStruct := ⟨y.left, hy, hy2⟩
  have hT : T = hU.default := hU.uniq T
  apply Over.OverMorphism.ext
  change T.l = hU.default.l
  rw [hT]

end GlobalTheory.DVRExt
