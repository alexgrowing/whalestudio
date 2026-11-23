import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import ReciprocityTheory.Automorphisms.PlaceA

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory

theorem localUnit_div_congr_one {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) (y : 𝓞 L)
    (hy : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) < 1) :
    y ∉ v.asIdeal ∧ ∃ k : Lˣ, (k : L) = (y : L) ∧
      Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1)
        ≤ WithZero.exp (-1 : ℤ) := by
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx']
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx']
    exact hy
  have hy2 : v.valuation L (algebraMap (𝓞 L) L y) = 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap, ← ReciprocityTheory.Aut.adic_algebraMap_R]
    exact hy1
  have hnot : y ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mp hy2
  have hy0 : (y : L) ≠ 0 := by
    intro h
    apply hnot
    have : y = 0 := by exact_mod_cast h
    rw [this]
    exact v.asIdeal.zero_mem
  refine ⟨hnot, Units.mk0 (y : L) hy0, rfl, ?_⟩
  have hk : ((atFin v (Units.mk0 (y : L) hy0) : (v.adicCompletion L)ˣ) : v.adicCompletion L)
      = algebraMap (𝓞 L) (v.adicCompletion L) y := rfl
  have hne : algebraMap (𝓞 L) (v.adicCompletion L) y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  have e : ((x * (atFin v (Units.mk0 (y : L) hy0))⁻¹ : (v.adicCompletion L)ˣ) :
      v.adicCompletion L) - 1 = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
        * (algebraMap (𝓞 L) (v.adicCompletion L) y)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hk, sub_mul, mul_inv_cancel₀ hne]
  rw [e, map_mul, map_inv₀, hy1, inv_one, mul_one]
  generalize Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) = g at hy
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem exists_nat_congr_of_absNorm_prime {L : Type} [Field L] [NumberField L]
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊤) {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm I = p) (y : 𝓞 L) :
    ∃ a : ℕ, y - (a : 𝓞 L) ∈ I := by
  have := Fact.mk hp
  have hcard : Nat.card (𝓞 L ⧸ I) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Nontrivial (𝓞 L ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h := mem_multiples_of_prime_card hcard (g := (1 : 𝓞 L ⧸ I))
    (g' := Ideal.Quotient.mk I y) one_ne_zero
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, map_natCast, ← ha]
  simp

open Classical in

theorem localUnit_congr_global :
    ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ), IsUnitAt v x → (∃ (k : Lˣ) (y : 𝓞 L), (k : L) = (y : L) ∧ y ∉ v.asIdeal ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ)) ∧ ∀ p : ℕ, p.Prime → Ideal.absNorm v.asIdeal = p → ∃ (a : ℕ) (k : Lˣ), a.Coprime p ∧ (k : L) = (a : L) ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
  intro L _ _ v x hx
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (x : v.adicCompletion L) (le_of_eq hx)
  refine ⟨?_, fun p hp hN => ?_⟩
  · obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx y hy
    exact ⟨k, y, hk, h1, h2⟩
  · obtain ⟨a, ha⟩ := exists_nat_congr_of_absNorm_prime v.asIdeal v.isPrime.ne_top hp hN y
    have hya : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L))) < 1 := by
      have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)))
          = v.valuation L (algebraMap (𝓞 L) L (y - (a : 𝓞 L))) :=
        ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L (y - (a : 𝓞 L)))
      rw [h3]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr ha
    have hxa : Valued.v ((x : v.adicCompletion L)
        - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)) < 1 := by
      have e : (x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)
          = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
            + algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)) := by
        rw [map_sub]; ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy hya)
    obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx (a : 𝓞 L) hxa
    refine ⟨a, k, ?_, by simpa using hk, h2⟩
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    rintro ⟨c, rfl⟩
    apply h1
    have hpm : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := hN ▸ Ideal.absNorm_mem v.asIdeal
    push_cast
    exact v.asIdeal.mul_mem_right _ hpm

end GlobalTheory
