import Formalism.ConjugateSelfDual.Statement

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.VB.Cmp

variable {K Ω' : Type*} [Field K] [NumberField K] [Field Ω'] [Algebra K Ω'] (A : ValuationSubring Ω')

theorem val_le_one (x : 𝓞 K) : A.valuation (algebraMap K Ω' (x : K)) ≤ 1 := by
  have hv : A.valuation.Integers A :=
    ⟨Subtype.val_injective, fun a => A.valuation_le_one a,
      fun {r} hr => ⟨⟨r, A.mem_of_valuation_le_one r hr⟩, rfl⟩⟩
  have hx : IsIntegral ℤ (algebraMap K Ω' (x : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap
  exact hv.isIntegral_iff_v_le_one.1 hx.tower_top

def ltIdeal : Ideal (𝓞 K) where
  carrier := {x | A.valuation (algebraMap K Ω' (x : K)) < 1}
  add_mem' := by
    intro a b ha hb
    have e : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by norm_cast
    show A.valuation (algebraMap K Ω' ((a + b : 𝓞 K) : K)) < 1
    rw [e, map_add]
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    have e : ((c • x : 𝓞 K) : K) = (c : K) * (x : K) := by rw [smul_eq_mul]; norm_cast
    show A.valuation (algebraMap K Ω' ((c • x : 𝓞 K) : K)) < 1
    rw [e, map_mul, map_mul]
    calc A.valuation (algebraMap K Ω' (c : K)) * A.valuation (algebraMap K Ω' (x : K))
        ≤ 1 * A.valuation (algebraMap K Ω' (x : K)) := mul_le_mul_of_nonneg_right (val_le_one A c) zero_le'
      _ = A.valuation (algebraMap K Ω' (x : K)) := one_mul _
      _ < 1 := hx

theorem mem_ltIdeal (x : 𝓞 K) : x ∈ ltIdeal (K := K) A ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 := by exact Iff.rfl

private theorem exists_placeOver_of_valuation_natCast_lt_one (n : ℕ) (hn : 0 < n) (h : A.valuation (n : Ω') < 1) :
    ∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧
      ∀ x : 𝓞 K, x ∈ v.asIdeal ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 := by
  have hprime : (ltIdeal (K := K) A).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, mem_ltIdeal]
      simp
    · intro x y hxy
      rw [mem_ltIdeal] at hxy
      rw [mem_ltIdeal, mem_ltIdeal]
      have e : ((x * y : 𝓞 K) : K) = (x : K) * (y : K) := by norm_cast
      rw [e, map_mul, map_mul] at hxy
      rcases lt_or_eq_of_le (val_le_one A x) with hx | hx
      · exact Or.inl hx
      rcases lt_or_eq_of_le (val_le_one A y) with hy | hy
      · exact Or.inr hy
      rw [hx, hy, one_mul] at hxy
      exact absurd hxy (lt_irrefl 1)
  have hmem : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K := K) A := by
    rw [mem_ltIdeal]
    simpa using h
  have hne : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨ltIdeal (K := K) A, hprime, fun hbot => hne (Ideal.mem_bot.1 (hbot ▸ hmem))⟩,
    fun x => (mem_ltIdeal A x).symm, fun x => mem_ltIdeal A x⟩

theorem exists_over_above_iff (l : ℕ) [Fact l.Prime] :
    (∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) ↔
      A.valuation (l : Ω') < 1 := by
  constructor
  · rintro ⟨v, hv, hl⟩
    have h := (hv _).2 hl
    simpa using h
  · intro h
    obtain ⟨v, hv, hmem⟩ := exists_placeOver_of_valuation_natCast_lt_one (K := K) A l (Fact.out : l.Prime).pos h
    exact ⟨v, hv, (hmem _).2 (by simpa using h)⟩

end Formalism.VB.Cmp
