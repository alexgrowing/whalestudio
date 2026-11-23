import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory

theorem placeBelow_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) (σ : E →+* ℂ) (la : HeightOneSpectrum (𝓞 c.F)) : ∃ w : HeightOneSpectrum (𝓞 E),
      ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ la.valuation c.F (embK c σ a) < 1 := by
  set f : 𝓞 E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (embF c σ) with hf
  have hemb : ∀ a : 𝓞 E, embK c σ a = algebraMap (𝓞 c.F) c.F (f a) := fun _ => rfl
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hZ : Ideal.comap (algebraMap ℤ (𝓞 c.F)) la.asIdeal ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxI (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hnI, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
  haveI : la.asIdeal.IsPrime := la.isPrime
  refine ⟨⟨la.asIdeal.comap f, Ideal.comap_isPrime f la.asIdeal, ?_⟩, fun a => ?_⟩
  · intro hbot
    have hmem : ((n : ℤ) : 𝓞 E) ∈ la.asIdeal.comap f := by
      rw [Ideal.mem_comap, map_intCast]
      simpa using hnI
    rw [hbot, Ideal.mem_bot] at hmem
    exact hn0 (by exact_mod_cast hmem)
  · show f a ∈ la.asIdeal ↔ _
    rw [hemb, HeightOneSpectrum.valuation_lt_one_iff_mem]

end GlobalTheory
