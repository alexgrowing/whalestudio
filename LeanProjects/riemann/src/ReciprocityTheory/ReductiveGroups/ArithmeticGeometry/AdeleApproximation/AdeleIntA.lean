import Mathlib

noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

def IsInt (b : FiniteAdeleRing R K) : Prop := ∀ v, b v ∈ v.adicCompletionIntegers K

private theorem val_R_lemma (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  first
  | exact (valuedAdicCompletion_eq_valuation (K := K) v r).trans (by rw [valuation_of_algebraMap])
  | exact (valuedAdicCompletion_eq_valuation' (R := R) v (algebraMap R K r)).trans
      (by rw [valuation_of_algebraMap])
  | (rw [← IsScalarTower.algebraMap_apply R K (v.adicCompletion K)];
      exact (valuedAdicCompletion_eq_valuation (K := K) v r).trans (by rw [valuation_of_algebraMap]))

theorem int_R (v : HeightOneSpectrum R) (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  first
  | (show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1;
      rw [val_R_lemma]; exact v.intValuation_le_one r)
  | exact coe_algebraMap_mem v r
  | exact coe_algebraMap_mem (K := K) v r

theorem val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := val_R_lemma v r

theorem exists_near (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ k : K, y - algebraMap K (v.adicCompletion K) k ∈ v.adicCompletionIntegers K := by
  have hU : IsOpen ((fun z => z - y) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_sub_right y)
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (R := R) (K := K) v).exists_mem_open hU
    ⟨y, by simp⟩
  refine ⟨k, ?_⟩
  have hk' : algebraMap K (v.adicCompletion K) k - y ∈ v.adicCompletionIntegers K := hk
  have := neg_mem hk'
  simpa [neg_sub] using this

theorem exists_den_local (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * y ∈ v.adicCompletionIntegers K := by
  first
  | (obtain ⟨b, hb, hyb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v y;
      exact ⟨b, nonZeroDivisors.ne_zero hb, by rw [mul_comm]; exact hyb⟩)
  | (obtain ⟨b, hb, hyb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (K := K) v y;
      exact ⟨b, nonZeroDivisors.ne_zero hb, by
        rw [mul_comm, IsScalarTower.algebraMap_apply R K (v.adicCompletion K)] at *; exact hyb⟩)
  | (obtain ⟨b, hb, hyb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v y;
      exact ⟨b, nonZeroDivisors.ne_zero hb, by
        simpa [mul_comm, IsScalarTower.algebraMap_apply R K (v.adicCompletion K)] using hyb⟩)

private theorem algK_apply_lemma_2 (v : HeightOneSpectrum R) (k : K) :
    (algebraMap K (FiniteAdeleRing R K) k) v = algebraMap K (v.adicCompletion K) k := by
  first
  | rfl
  | (simp; done)

private theorem algR_apply_lemma_3 (v : HeightOneSpectrum R) (r : R) :
    (algebraMap R (FiniteAdeleRing R K) r) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) := by
  first
  | rfl
  | (rw [IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K)]; exact algK_apply_lemma_2 v _)
  | (simp [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]; done)
  | (simp [IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K)]; done)

theorem exists_den (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by
  classical
  have hfin : {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite := by
    first
    | exact Filter.eventually_cofinite.mp b.2
    | exact b.2
  choose s hs0 hs using fun v => exists_den_local (R := R) (K := K) v (b v)
  refine ⟨∏ w ∈ hfin.toFinset, s w, Finset.prod_ne_zero_iff.mpr fun w _ => hs0 w, ?_⟩
  intro v
  rw [show (algebraMap R (FiniteAdeleRing R K) (∏ w ∈ hfin.toFinset, s w) * b) v =
      (algebraMap R (FiniteAdeleRing R K) (∏ w ∈ hfin.toFinset, s w)) v * b v from rfl,
    algR_apply_lemma_3]
  by_cases hvS : v ∈ hfin.toFinset
  · rw [← Finset.prod_erase_mul _ _ hvS, map_mul, map_mul, mul_assoc]
    exact mul_mem (int_R v _) (hs v)
  · have hb : b v ∈ v.adicCompletionIntegers K := by
      by_contra hc
      exact hvS (hfin.mem_toFinset.mpr hc)
    exact mul_mem (int_R v _) hb

theorem exists_approx_local (v : HeightOneSpectrum R) (c : v.adicCompletion K)
    (hc : c ∈ v.adicCompletionIntegers K) (r : R) (hr : r ≠ 0) :
    ∃ a : R, Valued.v (c - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by
  have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
  have hrv : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr hrK
  obtain ⟨k', hk'⟩ := exists_near v ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c)
  have h1 : Valued.v (c - algebraMap K _ (algebraMap R K r * k')) ≤ v.intValuation r := by
    have : c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k') =
        algebraMap K _ (algebraMap R K r) *
          ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c - algebraMap K _ k') := by
      rw [map_mul, mul_sub, ← mul_assoc, mul_inv_cancel₀ hrv, one_mul]
    rw [this, Valuation.map_mul, val_R]
    exact mul_le_of_le_one_right' hk'
  have hk : v.valuation K (algebraMap R K r * k') ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (((algebraMap R K r * k' : K)) : v.adicCompletion K) =
        c - (c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k')) := by
      rw [sub_sub_cancel]; rfl
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hc (h1.trans (v.intValuation_le_one r)))
  have hγ : v.intValuation r ≠ 0 := v.intValuation_ne_zero r hr
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk (Units.mk0 _ hγ)
  refine ⟨a, ?_⟩
  have e : c - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      (c - algebraMap K _ (algebraMap R K r * k')) -
        algebraMap K _ (algebraMap R K a - algebraMap R K r * k') := by
    rw [map_sub]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans (max_le h1 ?_)
  have := valuedAdicCompletion_eq_valuation' v (algebraMap R K a - algebraMap R K r * k')
  exact this.trans_le ha.le

theorem exists_approx (c : FiniteAdeleRing R K) (hc : IsInt c) (r : R) (hr : r ≠ 0) :
    ∃ a : R, ∀ v, Valued.v (c v - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by
  classical
  have hT : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {r}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr)
  choose a0 ha0 using fun v => exists_approx_local v (c v) (hc v) r hr
  obtain ⟨a, ha⟩ := exists_forall_sub_mem_ideal (s := hT.toFinset) (fun v => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {r})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a0 v.1)
  refine ⟨a, fun v => ?_⟩
  by_cases hv : v ∈ hT.toFinset
  · have h1 := ha v hv
    rw [← intValuation_le_pow_iff_mem, ← intValuation_eq_exp_neg_multiplicity v hr] at h1
    have e : c v - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
        (c v - algebraMap K _ (algebraMap R K (a0 v))) - algebraMap K _ (algebraMap R K (a - a0 v)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le (ha0 v) ?_)
    rw [val_R]; exact h1
  · have h1 : v.intValuation r = 1 := by
      rw [intValuation_eq_one_iff_mem_primeCompl]
      refine Ideal.mem_primeCompl_iff.mpr fun hmem => hv ?_
      rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hmem
    rw [h1]; exact sub_mem (hc v) (int_R v a)

theorem exists_approx_adele (b : FiniteAdeleRing R K) :
    ∃ u : K, IsInt (b - algebraMap K (FiniteAdeleRing R K) u) := by
  obtain ⟨r, hr, hrb⟩ := exists_den b
  obtain ⟨a, ha⟩ := exists_approx _ hrb r hr
  refine ⟨algebraMap R K a / algebraMap R K r, fun v => ?_⟩
  have hrK : algebraMap R K r ≠ 0 := by
    first
    | exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    | (rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hr)
    | exact fun h => hr ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hrv : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 := (map_ne_zero _).mpr hrK
  have h0 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hrv
  have hk' : algebraMap R K r * (algebraMap R K a / algebraMap R K r) = algebraMap R K a := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hrK, mul_one]
  have hc : (algebraMap R (FiniteAdeleRing R K) r * b) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v := by
    rw [show (algebraMap R (FiniteAdeleRing R K) r * b) v =
        (algebraMap R (FiniteAdeleRing R K) r) v * b v from rfl, algR_apply_lemma_3]
  have hsub : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v =
      b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) := by
    rw [show (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v =
        b v - (algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v from rfl,
      algK_apply_lemma_2]
  have key : (algebraMap R (FiniteAdeleRing R K) r * b) v -
        algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) *
        (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v := by
    rw [hc, hsub, mul_sub, ← map_mul (algebraMap K (v.adicCompletion K)), hk']
  have hv := ha v
  rw [key, map_mul, ← val_R_lemma (K := K) v r] at hv
  show Valued.v ((b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v) ≤ 1
  first
  | exact (mul_le_mul_left₀ h0).mp (by rwa [mul_one])
  | exact le_of_mul_le_mul_left (by rwa [mul_one]) (zero_lt_iff.mpr h0)
  | exact (mul_le_iff_le_one_right (zero_lt_iff.mpr h0)).mp hv

theorem isInt_zero : IsInt (0 : FiniteAdeleRing R K) := by
  intro v
  first
  | exact zero_mem _
  | (simp; done)

theorem isInt_add {a b : FiniteAdeleRing R K} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  intro v
  first
  | exact add_mem (ha v) (hb v)
  | simpa using add_mem (ha v) (hb v)

theorem isInt_mul {a b : FiniteAdeleRing R K} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  intro v
  first
  | exact mul_mem (ha v) (hb v)
  | simpa using mul_mem (ha v) (hb v)

theorem isInt_R (r : R) : IsInt (algebraMap R (FiniteAdeleRing R K) r) := by
  intro v
  rw [algR_apply_lemma_3]
  exact int_R v r

theorem mem_of_isInt (k : K) (h : IsInt (algebraMap K (FiniteAdeleRing R K) k)) :
    k ∈ (algebraMap R K).range := by
  apply mem_integers_of_valuation_le_one
  intro v
  have hv : Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1 := by
    rw [← algK_apply_lemma_2 v k]
    exact h v
  first
  | exact (valuedAdicCompletion_eq_valuation' (R := R) v k).symm.trans_le hv
  | exact (valuedAdicCompletion_eq_valuation' v k).symm.trans_le hv
  | (rw [← valuedAdicCompletion_eq_valuation' (R := R) v k]; exact hv)

end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
