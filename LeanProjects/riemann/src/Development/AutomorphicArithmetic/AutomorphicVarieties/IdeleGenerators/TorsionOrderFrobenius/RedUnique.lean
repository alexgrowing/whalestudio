import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

namespace UpperTheory.V.Sd.Tw

variable {K : Type} [Field K] [NumberField K]

private theorem red_field (v : HeightOneSpectrum (𝓞 K)) (a : K) :
    Valued.v (algebraMap K (v.adicCompletion K) a) = v.valuation K a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem red_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    Valued.v (algebraMap K (v.adicCompletion K) (a : K)) = v.intValuation a := by
  rw [red_field]
  exact v.valuation_of_algebraMap a

private theorem red_nat (v : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    Valued.v (N : v.adicCompletion K) = v.intValuation (N : 𝓞 K) := by
  rw [← red_int]
  congr 1
  have : (((N : 𝓞 K)) : K) = (N : K) := map_natCast (algebraMap (𝓞 K) K) N
  rw [this, map_natCast]

private theorem red_approx (v : HeightOneSpectrum (𝓞 K)) {n : 𝓞 K} (hn : n ≠ 0)
    {y : v.adicCompletion K} (hy : Valued.v y ≤ 1) :
    ∃ a : 𝓞 K, Valued.v (y - algebraMap K (v.adicCompletion K) (a : K)) ≤ v.intValuation n := by
  have h0 : v.intValuation n ≠ 0 := v.intValuation_ne_zero n hn
  have ho : IsOpen {y : v.adicCompletion K | Valued.v y < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion K) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  have h1 : IsOpen {z : v.adicCompletion K |
      Valued.v ((y - z) * (algebraMap K (v.adicCompletion K) (n : K))⁻¹) < 1} :=
    ho.preimage ((continuous_const.sub continuous_id).mul continuous_const)
  obtain ⟨t, ht⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open h1
    ⟨y, by simp⟩
  have ht : Valued.v ((y - algebraMap K (v.adicCompletion K) t) *
    (algebraMap K (v.adicCompletion K) (n : K))⁻¹) < 1 := ht
  rw [map_mul, map_inv₀, red_int, mul_inv_lt_iff₀ (zero_lt_iff.2 h0), one_mul] at ht
  have ht1 : v.valuation K t ≤ 1 := by
    rw [← red_field, ← sub_sub_cancel y (algebraMap K (v.adicCompletion K) t)]
    exact Valuation.map_sub_le _ hy (ht.le.trans (v.intValuation_le_one n))
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer ht1 (Units.mk0 _ h0)
  refine ⟨a, ?_⟩
  have e : y - algebraMap K (v.adicCompletion K) (a : K) =
      (y - algebraMap K (v.adicCompletion K) t) -
        algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a - t) := by
    rw [map_sub]; ring
  rw [e]
  refine Valuation.map_sub_le _ ht.le ?_
  rw [red_field]
  exact ha.le

private theorem red_exists {n : 𝓞 K} (hn : n ≠ 0)
    (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (hy : ∀ v, Valued.v (y v) ≤ 1) :
    ∃ a : 𝓞 K, ∀ v : HeightOneSpectrum (𝓞 K), n ∈ v.asIdeal →
      Valued.v (y v - algebraMap K (v.adicCompletion K) (a : K)) ≤ v.intValuation n := by
  classical
  have hS : {v : HeightOneSpectrum (𝓞 K) | n ∈ v.asIdeal}.Finite := by
    have := Ideal.finite_factors (I := Ideal.span {n}) (by simpa using hn)
    simpa only [Ideal.dvd_span_singleton] using this
  choose f hf using fun v : HeightOneSpectrum (𝓞 K) => red_approx v hn (hy v)
  have he : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : ℕ, v.intValuation n = WithZero.exp (-(e : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg hn⟩
  choose e he using he
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hS.toFinset)
    (fun v => v.asIdeal) e (fun v _ => v.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun v => f v.1)
  refine ⟨a, fun v hv => ?_⟩
  have h1 := ha v (hS.mem_toFinset.2 hv)
  rw [← v.intValuation_le_pow_iff_mem, ← he, ← red_int] at h1
  have e1 : y v - algebraMap K (v.adicCompletion K) (a : K) =
      (y v - algebraMap K (v.adicCompletion K) (f v : K)) -
        algebraMap K (v.adicCompletion K) ((a - f v : 𝓞 K) : K) := by
    have : ((a - f v : 𝓞 K) : K) = (a : K) - (f v : K) := map_sub (algebraMap (𝓞 K) K) _ _
    rw [this, map_sub]; ring
  rw [e1]
  exact Valuation.map_sub_le _ (hf v) h1

private theorem red_unique {n : 𝓞 K} (hn : n ≠ 0)
    (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) {a b : 𝓞 K}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), n ∈ v.asIdeal →
      Valued.v (y v - algebraMap K (v.adicCompletion K) (a : K)) ≤ v.intValuation n)
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), n ∈ v.asIdeal →
      Valued.v (y v - algebraMap K (v.adicCompletion K) (b : K)) ≤ v.intValuation n) :
    Ideal.Quotient.mk (Ideal.span {n}) a = Ideal.Quotient.mk (Ideal.span {n}) b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hle : ∀ v : HeightOneSpectrum (𝓞 K), v.intValuation (a - b) ≤ v.intValuation n := by
    intro v
    by_cases hv : n ∈ v.asIdeal
    · have := Valuation.map_sub_le _ (hb v hv) (ha v hv)
      rw [sub_sub_sub_cancel_left, ← map_sub] at this
      have e : ((a - b : 𝓞 K) : K) = (a : K) - (b : K) := map_sub (algebraMap (𝓞 K) K) _ _
      rwa [← e, red_int] at this
    · rw [v.intValuation_eq_one_iff.2 hv]
      exact v.intValuation_le_one _
  have hn' : algebraMap (𝓞 K) K n ≠ 0 := by simpa using hn
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
    (algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K n) (fun v => by
      rw [map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
      exact div_le_one_of_le₀ (hle v) zero_le)
  refine ⟨c, IsFractionRing.injective (𝓞 K) K ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ hn']

end UpperTheory.V.Sd.Tw

theorem UpperTheory.V.Sd.Tw.red :
    ∀ (K : Type) [Field K] [NumberField K] (N : ℕ), N ≠ 0 →
        ∃ red : ↥(GlobalTheory.Mem.Chr.unitIdl K) →* (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ,
          ∀ (a : ↥(GlobalTheory.Mem.Chr.unitIdl K)) (r : 𝓞 K),
            (∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∈ v.asIdeal →
              Valued.v (((a : Ideles K) : AdeleRing (𝓞 K) K).2 v - algebraMap K (v.adicCompletion K) (r : K)) ≤
                Valued.v (N : v.adicCompletion K)) →
            ((red a : (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ) : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) = Ideal.Quotient.mk _ r := by
  intro K _ _ N hN
  have hn : (N : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hN
  choose f hf using fun a : GlobalTheory.Mem.Chr.unitIdl K =>
    red_exists hn (fun v => ((a : Ideles K) : AdeleRing (𝓞 K) K).2 v) (fun v => (a.2 v).le)
  let φ : GlobalTheory.Mem.Chr.unitIdl K →* (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) :=
    { toFun := fun a => Ideal.Quotient.mk _ (f a)
      map_one' := by
        rw [← map_one (Ideal.Quotient.mk _)]
        refine red_unique hn _ (hf 1) fun v _ => ?_
        show Valued.v ((1 : v.adicCompletion K) - _) ≤ _
        simp
      map_mul' := fun a b => by
        rw [← map_mul]
        refine red_unique hn _ (hf (a * b)) fun v hv => ?_
        show Valued.v (((a : Ideles K) : AdeleRing (𝓞 K) K).2 v *
          ((b : Ideles K) : AdeleRing (𝓞 K) K).2 v - _) ≤ _
        have e0 : ((f a * f b : 𝓞 K) : K) = (f a : K) * (f b : K) := map_mul (algebraMap (𝓞 K) K) _ _
        have e1 : ∀ x y p q : v.adicCompletion K, x * y - p * q = x * (y - q) + q * (x - p) :=
          fun x y p q => by ring
        rw [e0, map_mul, e1]
        refine Valuation.map_add_le _ ?_ ?_
        · rw [map_mul, a.2 v, one_mul]
          exact hf b v hv
        · rw [map_mul, red_int]
          exact (mul_le_of_le_one_left' (v.intValuation_le_one _)).trans (hf a v hv) }
  refine ⟨φ.toHomUnits, fun a r h => ?_⟩
  show Ideal.Quotient.mk _ (f a) = _
  exact red_unique hn _ (hf a) fun v hv => by rw [← red_nat]; exact h v hv
