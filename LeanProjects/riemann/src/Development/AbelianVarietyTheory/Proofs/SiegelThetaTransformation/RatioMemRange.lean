import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfEqComplex
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.ConstRatio

theorem ratio_mem_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Type) [Field T] [IsAlgClosed T] [Algebra c.F T]
    (u u' : FrPt Xo c T → T)
    (hu : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u y) = u z)
    (hu' : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u' y) = u' z)
    (z : T) (h : ∀ y, u' y = z * u y) (y : FrPt Xo c T) (hy : u y ≠ 0) :
    z ∈ Set.range (algebraMap c.F T) := by
  refine GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv z fun σ => ?_
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T T σ.toAlgHom y
  have h1 := hu _ _ _ hy'
  have h2 := hu' _ _ _ hy'
  rw [h y, h y', map_mul, ← h1] at h2
  have hne : σ.toAlgHom (u y) ≠ 0 := by
    simpa using hy
  exact mul_right_cancel₀ hne h2

theorem exists_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (J : Type) (u u' : J → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u j S y) = u j T z)) → (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' j S y) = u' j T z)) → ∀ z : ℂ, IsMu z → (∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u' j ℂ _ s.toAlgebra y = z * @u j ℂ _ s.toAlgebra y) → ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧ ∀ j (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u' j S y = algebraMap c.F S z₀ * u j S y := by
  intro E _ _ _ H Dw l Xo c s J u u' hu hu' z hz h
  have key : ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧
      ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra),
        @u' j ℂ _ s.toAlgebra y = s z₀ * @u j ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u j ℂ _ s.toAlgebra y = 0
    · refine ⟨1, ⟨1, one_pos, one_pow 1⟩, fun j y => ?_⟩
      rw [h j y, h0 j y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨j, y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u j ℂ _ s.toAlgebra) (@u' j ℂ _ s.toAlgebra)
        (@hu j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@hu' j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z (h j) y hy
      have hz₀' : s z₀ = z := hz₀
      obtain ⟨m, hm, hzm⟩ := hz
      refine ⟨z₀, ⟨m, hm, s.injective ?_⟩, fun j y => ?_⟩
      · rw [map_pow, hz₀', hzm, map_one]
      · rw [hz₀', h j y]
  obtain ⟨z₀, hk, hz₀⟩ := key
  refine ⟨z₀, hk, fun j => ?_⟩
  refine GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s (u' j) (fun S _ _ y => algebraMap c.F S z₀ * u j S y) (hu' j) ?_ ?_
  · intro S T _ _ _ _ φ y y' hyy
    rw [map_mul, φ.commutes, hu j S T φ y y' hyy]
  · intro y
    exact hz₀ j y

end GlobalTheory.ConstRatio
