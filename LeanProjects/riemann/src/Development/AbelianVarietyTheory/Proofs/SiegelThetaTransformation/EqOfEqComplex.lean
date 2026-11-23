import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstIffSecondAndResiduals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.NaturalValues

theorem eq_of_points {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] [Algebra.FiniteType K R]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] {x y : R} (h : ∀ φ : R →ₐ[K] Ω, φ x = φ y) : x = y := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  rw [← sub_eq_zero]
  have hb : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance ((Ideal.isRadical_iff_quotient_reduced _).2
      (isReduced_of_injective (RingEquiv.quotientBot R) (RingEquiv.quotientBot R).injective))
  rw [← Ideal.mem_bot, ← hb]
  refine Ideal.mem_sInf.2 fun {m} hm => ?_
  haveI := hm.2
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  let ψ : (R ⧸ m) →ₐ[K] Ω := IsAlgClosed.lift
  have e := h (ψ.comp (Ideal.Quotient.mkₐ K m))
  rw [← sub_eq_zero, ← map_sub, AlgHom.comp_apply, map_eq_zero] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e

theorem eq_of_eq_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (u u' : ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u S y) = u T z) → (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' S y) = u' T z) → (∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u ℂ _ s.toAlgebra y = @u' ℂ _ s.toAlgebra y) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u S y = u' S y := by
  intro E _ _ _ H Dw l Xo c s u u' hu hu' hc S _ _ y
  have hF := GlobalTheory.RepCompare.frameLaws Xo c
  letI := s.toAlgebra
  refine eq_of_locM (K := c.F) fun m hm => ?_
  obtain ⟨A, v, cw, -, -, -, ⟨wm, h1, h2⟩, -⟩ := hF.cover S y y rfl m
  have e : u A.R v = u' A.R v := by
    refine eq_of_points (K := c.F) (Ω := ℂ) fun φ => ?_
    obtain ⟨z, hz⟩ := hF.bc _ _ φ v
    rw [hu _ _ φ v z hz, hu' _ _ φ v z hz]
    exact hc z
  rw [hu _ _ _ y wm h1, hu' _ _ _ y wm h1, ← hu _ _ cw v wm h2, ← hu' _ _ cw v wm h2, e]

end GlobalTheory.NaturalValues
