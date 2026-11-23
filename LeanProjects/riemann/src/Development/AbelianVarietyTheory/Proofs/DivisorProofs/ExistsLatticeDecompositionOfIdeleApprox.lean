import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

namespace GlobalTheory.LatDecomp

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem finiteAdeleMap_algebraMap (a : K) :
    finiteAdeleMap K E (algebraMap K (Af K) a) = algebraMap E (Af E) (algebraMap K E a) :=
  FiniteAdeleRing.ext _ fun w => finiteCompletionMap_coe K E w a

theorem finiteAdeleMap_integral {z : Af K} (hz : ∀ v, Valued.v (z v) ≤ 1) (w : HeightOneSpectrum (𝓞 E)) :
    (finiteAdeleMap K E z) w ∈ w.adicCompletionIntegers E :=
  finiteCompletionMap_mapsTo K E w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz _))

theorem algebraMap_integral (s : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (s : E)) w ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_le_one s

theorem exists_nat_mul_integral (a : Af E) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ w, ((d : Af E) * a) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨β, hβ0, hβ⟩ := GlobalTheory.Idele.exists_mul_integral (R := 𝓞 E) (K := E) a
  have hmem : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : 𝓞 E) ∈ Ideal.span {β} := Ideal.absNorm_mem _
  obtain ⟨g0, hg0⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨Ideal.absNorm (Ideal.span {β}), ?_, fun w => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hβ0
  · have e : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : Af E) =
        algebraMap E (Af E) ((g0 : 𝓞 E) : E) * algebraMap E (Af E) (algebraMap (𝓞 E) E β) := by
      rw [← map_mul]
      have := congrArg (fun r : 𝓞 E => algebraMap E (Af E) (r : E)) hg0
      simp only [map_natCast] at this
      rw [← this]; push_cast; rfl
    rw [e, _root_.mul_assoc]
    exact mul_mem (algebraMap_integral g0 w) ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hβ w))

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_good {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) (e : E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z : Af E, (∀ w, z w ∈ w.adicCompletionIntegers E) →
      z * algebraMap E (Af E) ((N : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_integral (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E))
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm c * d, Nat.mul_ne_zero hN hd0, fun z hz => ?_⟩
  have h := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c)
    (y := z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) (fun w => mul_mem (hz w) (hd w))
  have e1 : z * algebraMap E (Af E) (((Ideal.absNorm c * d : ℕ) : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) =
      algebraMap E (Af E) (algebraMap (OF E) E ((Ideal.absNorm c : ℕ) : OF E)) *
        (z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) := by
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e1]; exact h

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

theorem exists_decomp : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E]
    (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ x x' : E,
    ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
    ∃ (m : ℕ) (b : Fin m → E) (a a' : Fin m → K), (∀ k (r : 𝓞 K), algebraMap K E (r : K) * b k ∈ lattice c y) ∧
      x' = ∑ k, algebraMap K E (a' k) * b k ∧ x - ∑ k, algebraMap K E (a k) * b k ∈ lattice c y ∧
      ∀ k (v : HeightOneSpectrum (𝓞 K)),
        Valued.v (((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) v) ≤ 1 := by
  intro K _ _ E _ _ _ _ t c y hc x x' hx
  haveI : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  set B := Module.finBasis K E
  set yi : Af E := ((y⁻¹ : (Af E)ˣ) : Af E)
  choose N hN0 hN using fun k => exists_nat_mul_good hc y (B k)
  set b : Fin (Module.finrank K E) → E := fun k => (N k : E) * B k with hb
  set a' : Fin (Module.finrank K E) → K := fun k => B.repr x' k / (N k : K) with ha'
  have hNK : ∀ k, (N k : K) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hN0 k)

  have happrox : ∀ z : Af K, ∃ a : K, ∀ v, Valued.v ((z - algebraMap K (Af K) a) v) ≤ 1 := fun z => by
    obtain ⟨a, u, hu, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat K 1 one_pos).1 z
    refine ⟨a, fun v => ?_⟩
    rw [e, one_smul, add_sub_cancel_left]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hu v)
  choose a ha using fun k => happrox ((t : Af K) * algebraMap K (Af K) (a' k))
  have hx' : x' = ∑ k, algebraMap K E (a' k) * b k := by
    conv_lhs => rw [← B.sum_repr x']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, hb, ha']
    simp only
    rw [← _root_.mul_assoc, ← map_natCast (algebraMap K E), ← map_mul, div_mul_cancel₀ _ (hNK k)]
  refine ⟨Module.finrank K E, b, a, a', fun k r => ?_, hx', ?_, ha⟩
  ·
    have hr : IsIntegral ℤ (algebraMap K E (r : K)) := (RingOfIntegers.isIntegral_coe r).algebraMap
    have h := hN k (algebraMap E (Af E) ((⟨algebraMap K E (r : K), hr⟩ : 𝓞 E) : E))
      (algebraMap_integral ⟨algebraMap K E (r : K), hr⟩)
    rw [mem_lattice, map_mul]
    exact h
  ·
    have hT : (upIdele K E t : Af E) = finiteAdeleMap K E (t : Af K) := rfl
    have hkey : algebraMap E (Af E) (x - ∑ k, algebraMap K E (a k) * b k) * yi =
        -(((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * yi) +
          ∑ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi := by
      have e2 : ∀ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi =
          finiteAdeleMap K E (t : Af K) * (algebraMap E (Af E) (algebraMap K E (a' k) * b k)) * yi -
            algebraMap E (Af E) (algebraMap K E (a k) * b k) * yi := fun k => by
        simp only [map_sub, map_mul, finiteAdeleMap_algebraMap]
        ring
      rw [Finset.sum_congr rfl fun k _ => e2 k, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.mul_sum, ← map_sum, ← map_sum, ← hx', hT, map_sub]
      ring
    rw [mem_lattice, hkey]
    refine add_mem (neg_mem hx) (Subring.sum_mem _ fun k _ => ?_)
    exact hN k _ (finiteAdeleMap_integral (ha k))

end GlobalTheory.LatDecomp

example : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c → ∃ (m : ℕ) (b : Fin m → E) (a a' : Fin m → K), (∀ k (r : 𝓞 K), algebraMap K E (r : K) * b k ∈ lattice c y) ∧ x' = ∑ k, algebraMap K E (a' k) * b k ∧ x - ∑ k, algebraMap K E (a k) * b k ∈ lattice c y ∧ ∀ k (v : HeightOneSpectrum (𝓞 K)), Valued.v (((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) v) ≤ 1 := GlobalTheory.LatDecomp.exists_decomp
