import Mathlib
import Formalism.LocalRingCardinality.DataForms

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.Core.Int.ProdPrimePow

theorem vAdd_eq_count {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ≠ 0) :
    vAdd v x = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
  have key : ∀ r : 𝓞 K, r ≠ 0 → v.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp
      (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by
    intro r hr
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v (by simpa using hr)]
    have := v.valuation_of_algebraMap (K := K) r
    rw [HeightOneSpectrum.intValuation_if_neg _ hr] at this
    exact this
  have hv : v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; simp at hx
    have hb1 : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
    have ha1 : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha0
    rw [map_div₀, key a ha0, key b hb0, div_eq_mul_inv (algebraMap (𝓞 K) K a),
      ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha1)
        (FractionalIdeal.spanSingleton_ne_zero_iff.2 (inv_ne_zero hb1)),
      ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, ← WithZero.exp_sub]
    congr 1; ring
  unfold vAdd
  rw [hv, WithZero.log_exp, neg_neg]

theorem vAdd_ge_of_mem_prod_zpow :
    ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [DecidableEq ι]
      (e : ι ≃ HeightOneSpectrum (𝓞 K)) (S : Finset ι) (n : ι → ℤ) (a : K),
      a ∈ (∏ w ∈ S, ((e w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(n w))) →
      ∀ w : ι, a = 0 ∨ (if w ∈ S then -(n w) else 0) ≤ vAdd (e w) a := by
  intro K _ _ ι _ e S n a ha w
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  right
  have hne : ∀ i ∈ S, ((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i)) ≠ 0 := fun i _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (e i).ne_bot)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≤
      ∏ i ∈ S, ((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i)) :=
    (FractionalIdeal.spanSingleton_le_iff_mem).2 ha
  have hmono := FractionalIdeal.count_mono K (e w)
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0) hle
  rw [FractionalIdeal.count_prod K (e w) S _ hne] at hmono
  have hterm : ∀ i ∈ S, FractionalIdeal.count K (e w)
      (((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i))) = if w = i then -(n i) else 0 := by
    intro i _
    by_cases hwi : w = i
    · subst hwi
      rw [if_pos rfl, FractionalIdeal.count_zpow_self]
    · rw [if_neg hwi, FractionalIdeal.count_zpow,
        FractionalIdeal.count_maximal_coprime K (e w) (fun h => hwi (e.injective h).symm), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq] at hmono
  rw [vAdd_eq_count (e w) ha0]
  exact hmono

end GlobalTheory.Core.Int.ProdPrimePow
