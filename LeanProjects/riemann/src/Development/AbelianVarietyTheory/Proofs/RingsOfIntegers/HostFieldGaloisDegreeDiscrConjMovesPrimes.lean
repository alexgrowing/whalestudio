import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.PlaceInt

theorem host_bar_eq_smul (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (x : 𝓞 D.host.E) :
    H.bar x = D.host.conj • x := by
  apply RingOfIntegers.ext
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply φ x).symm

theorem host_galois_discr_moves : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  intro D H
  refine ⟨D.host.galois, D.host.der.finrank_E, D.host.der.discr_primes.1, ?_⟩
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, fun P hP hmem => ?_⟩
    by_contra hall
    push Not at hall
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hpp).irreducible
    have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 D.host.E) (p : ℤ) ∈ P
      rw [map_natCast]
      exact hmem
    have hbb : ∀ x : 𝓞 D.host.E, H.bar (H.bar x) = x := fun x => by
      apply RingOfIntegers.ext
      rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
    refine D.host.der.decompConj p hpp (Nat.dvd_of_mem_primeFactors hp) P ?_
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (D.host.conj)⁻¹ • x = H.bar x := by
      rw [inv_smul_eq_iff, ← host_bar_eq_smul D H, hbb]
    rw [hinv]
    refine ⟨fun h => ?_, hall x⟩
    have := hall _ h
    rwa [hbb] at this

end GlobalTheory.PlaceInt
