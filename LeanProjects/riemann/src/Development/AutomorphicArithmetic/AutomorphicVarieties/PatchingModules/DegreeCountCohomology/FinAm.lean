import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.finAm :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m g : ℕ), Finite (x.Am m) ∧ Nat.card (x.Am m) = Nat.card x.K ^ m ∧ Finite (DD (x.Am m) g) ∧ (∀ y : x.Am m, l • y = 0) ∧ (∀ y : DD (x.Am m) g, l • y = 0) ∧ (algebraMap x.A (x.Am m) x.t) ^ m = 0 ∧ (algebraMap x.A (DD (x.Am m) g) x.t) ^ m = 0 ∧ (l ≠ 2 → IsUnit (2 : x.A)) ∧ CharP x.K l := by
  intro l _ F n x m g
  obtain ⟨h1, h2, -, -, h5, -⟩ := UpperTheory.V.Pa.am_fin l F n x m g
  have hA : (l : x.A) = 0 := h5
  have e : (l : x.K) = 0 := by
    have := congrArg (PowerSeries.constantCoeff (R := x.K)) hA
    rwa [map_natCast, map_zero] at this
  have hc : CharP x.K l := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 e
  have hAm : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)), hA, map_zero]
  have hDD : (l : DD (x.Am m) g) = 0 := by
    rw [← map_natCast (DD.C (X := x.Am m) (g := g)), hAm, map_zero]
  haveI := h1
  have ht : (algebraMap x.A (x.Am m) x.t) ^ m = 0 := by
    rw [← map_pow, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  refine ⟨h1, h2, Finite.of_equiv _ DD.equiv.symm, fun y => by rw [nsmul_eq_mul, hAm, zero_mul],
    fun y => by rw [nsmul_eq_mul, hDD, zero_mul], ht, ?_, ?_, hc⟩
  · show (DD.C (algebraMap x.A (x.Am m) x.t)) ^ m = 0
    rw [← map_pow, ht, map_zero]
  · intro hl
    show IsUnit (2 : PowerSeries x.K)
    rw [PowerSeries.isUnit_iff_constantCoeff, map_ofNat]
    apply Ne.isUnit
    intro h2
    have h2' : ((2 : ℕ) : x.K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff x.K l] at h2'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2')
