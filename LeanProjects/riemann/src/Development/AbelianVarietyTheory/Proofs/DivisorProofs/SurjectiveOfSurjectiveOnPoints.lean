import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ComplexAbVarSurj

theorem surjective_of_surjective_points : ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (ψ : A ⟶ X), IsAbelianScheme A → IsAbelianScheme X →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) → Surjective ψ.left := by
  intro A X _ _ ψ hA hX h
  have hAp : IsProper A.hom := hA.proper
  have hXp : IsProper X.hom := hX.proper
  have : UniversallyClosed (ψ.left ≫ X.hom) := by rw [Over.w]; infer_instance
  have : UniversallyClosed ψ.left := UniversallyClosed.of_comp_of_isSeparated ψ.left X.hom
  have hcl : IsClosed (Set.range ψ.left) := ψ.left.isClosedMap.isClosed_range
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let pt : Spec (CommRingCat.of ℂ) := IsLocalRing.closedPoint ℂ
  have hsub : closedPoints X.left ⊆ Set.range ψ.left := by
    intro z hz
    obtain ⟨x, hx⟩ := h (Over.homMk (pointOfClosedPoint (K := ℂ) X.hom z hz)
      (pointOfClosedPoint_comp (K := ℂ) X.hom z hz))
    refine ⟨x.left pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
    exact pointOfClosedPoint_apply (K := ℂ) X.hom z hz pt
  have hall : Set.range ψ.left = Set.univ := by
    have := closure_mono hsub
    rw [closure_closedPoints, hcl.closure_eq] at this
    exact Set.eq_univ_of_univ_subset this
  exact ⟨Set.range_eq_univ.mp hall⟩

end GlobalTheory.ComplexAbVarSurj
