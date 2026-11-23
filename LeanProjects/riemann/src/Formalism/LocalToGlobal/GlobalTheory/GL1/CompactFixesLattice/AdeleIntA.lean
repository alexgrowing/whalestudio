import Mathlib

noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

def IsInt (b : FiniteAdeleRing R K) : Prop := ∀ v, b v ∈ v.adicCompletionIntegers K

private theorem memO_lemma (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 := by
  first
  | exact IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers ..
  | exact Iff.rfl
  | exact Valuation.mem_valuationSubring_iff _ _
  | simp [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

private theorem valR_lemma_2 (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  first
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans
      (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v _)
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) v _).trans
      (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v _)
  | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])
  | (erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])
  | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])
  | simp [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]

theorem int_R (v : HeightOneSpectrum R) (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [memO_lemma, valR_lemma_2]
  first
  | exact v.intValuation_le_one r
  | exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v r
  | exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one (v := v) r

theorem val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := valR_lemma_2 v r

theorem exists_near (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ k : K, y - algebraMap K (v.adicCompletion K) k ∈ v.adicCompletionIntegers K := by
  have hd : ∀ y : v.adicCompletion K, y ∈ closure (Set.range (algebraMap K (v.adicCompletion K))) := by
    first
    | exact fun y => UniformSpace.Completion.denseRange_coe y
    | exact UniformSpace.Completion.denseRange_coe
    | (intro y; exact (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := R) K v) y)
    | (intro y; exact (Valuation.Completion.denseRange_coe (v.valuation K)) y)
    | (unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion Valuation.Completion;
        exact UniformSpace.Completion.denseRange_coe)
    | (unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion;
        exact UniformSpace.Completion.denseRange_coe)
    | (delta IsDedekindDomain.HeightOneSpectrum.adicCompletion;
        exact UniformSpace.Completion.denseRange_coe)
  have hN : {z : v.adicCompletion K | Valued.v (z - y) < 1} ∈ nhds y := by
    first
    | exact Valued.mem_nhds.2 ⟨1, fun z hz => by simpa using hz⟩
    | (rw [Valued.mem_nhds]; exact ⟨1, fun z hz => by simpa using hz⟩)
    | exact (Valued.mem_nhds (x := y)).2 ⟨1, fun z hz => by simpa using hz⟩
  obtain ⟨_, hz, k, rfl⟩ := mem_closure_iff_nhds.1 (hd y) _ hN
  have hz' : Valued.v (algebraMap K (v.adicCompletion K) k - y) < 1 := hz
  refine ⟨k, (memO_lemma v _).2 ?_⟩
  first
  | (rw [Valuation.map_sub_swap]; exact le_of_lt hz')
  | (rw [← neg_sub, Valuation.map_neg]; exact le_of_lt hz')

theorem exists_den_local (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * y ∈ v.adicCompletionIntegers K := by
  obtain ⟨k, hk⟩ := exists_near v y
  obtain ⟨a, b, hb, hab⟩ :
      ∃ a b : R, b ∈ nonZeroDivisors R ∧ algebraMap R K a / algebraMap R K b = k := by
    first
    | exact IsFractionRing.div_surjective (A := R) k
    | (obtain ⟨a, b, h⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) k;
        exact ⟨a, b, b.2, by rw [← h, IsFractionRing.mk'_eq_div]⟩)
  subst hab
  have hb0 : b ≠ 0 := by
    first
    | exact nonZeroDivisors.ne_zero hb
    | exact mem_nonZeroDivisors_iff_ne_zero.1 hb
  have hbK : algebraMap R K b ≠ 0 := by
    first
    | exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    | exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb0
  refine ⟨b, hb0, ?_⟩
  have e1 : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
    first
    | (field_simp; done)
    | (rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ hbK)
    | (field_simp; ring)
  have e2 : algebraMap K (v.adicCompletion K) (algebraMap R K b) *
      (y - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K b)) +
      algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      algebraMap K (v.adicCompletion K) (algebraMap R K b) * y := by
    rw [mul_sub, ← map_mul (algebraMap K (v.adicCompletion K)), e1, sub_add_cancel]
  rw [← e2]
  exact add_mem (mul_mem (int_R v b) hk) (int_R v a)

private theorem fin_lemma_3 (b : FiniteAdeleRing R K) :
    {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite := by
  first
  | exact Filter.eventually_cofinite.1 b.2
  | exact b.2
  | exact Filter.eventually_cofinite.1 b.property
  | (have h := b.2; rw [Filter.eventually_cofinite] at h; exact h)

private theorem mulApp_lemma_4 (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := by
  first
  | rfl
  | simp
  | exact RestrictedProduct.mul_apply a b v

private theorem algApp_lemma_5 (r : R) (v : HeightOneSpectrum R) :
    (algebraMap R (FiniteAdeleRing R K) r) v = algebraMap K (v.adicCompletion K) (algebraMap R K r) := by
  first
  | rfl
  | (rw [IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K)]; rfl)
  | simp
  | (simp; rfl)

theorem exists_den (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by
  classical
  have hS := fin_lemma_3 b
  choose s hs0 hs using fun w : HeightOneSpectrum R => exists_den_local w (b w)
  refine ⟨∏ w ∈ hS.toFinset, s w, Finset.prod_ne_zero_iff.2 (fun w _ => hs0 w), ?_⟩
  intro v
  rw [mulApp_lemma_4, algApp_lemma_5]
  by_cases hv : v ∈ hS.toFinset
  · rw [← Finset.mul_prod_erase hS.toFinset s hv]
    simp only [map_mul]
    rw [show ∀ x y z : v.adicCompletion K, x * y * z = y * (x * z) from
      fun x y z => by ring]
    exact mul_mem (int_R v _) (hs v)
  · have hb : b v ∈ v.adicCompletionIntegers K := by
      by_contra h
      exact hv (hS.mem_toFinset.2 h)
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

private theorem algKApp_lemma_6 (k : K) (v : HeightOneSpectrum R) :
    (algebraMap K (FiniteAdeleRing R K) k) v = algebraMap K (v.adicCompletion K) k := by
  first
  | rfl
  | simp
  | (simp; rfl)

theorem exists_approx_adele (b : FiniteAdeleRing R K) :
    ∃ u : K, IsInt (b - algebraMap K (FiniteAdeleRing R K) u) := by
  obtain ⟨r, hr, hrb⟩ := exists_den b
  obtain ⟨a, ha⟩ := exists_approx _ hrb r hr
  have hrK : algebraMap R K r ≠ 0 := by
    first
    | exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    | exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr
  refine ⟨algebraMap R K a / algebraMap R K r, ?_⟩
  intro v
  have hv := ha v
  rw [mulApp_lemma_4, algApp_lemma_5] at hv
  have hsub : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v
      = b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) := by
    first
    | rfl
    | simp [algKApp_lemma_6]
    | (rw [← algKApp_lemma_6]; rfl)
  rw [hsub, memO_lemma]
  have e1 : algebraMap R K r * (algebraMap R K a / algebraMap R K r) = algebraMap R K a := by
    first
    | (field_simp; done)
    | (rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ hrK)
    | (field_simp; ring)
  have e2 : algebraMap K (v.adicCompletion K) (algebraMap R K r) *
      (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r)) =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v - algebraMap K (v.adicCompletion K) (algebraMap R K a) := by
    rw [mul_sub, ← map_mul (algebraMap K (v.adicCompletion K)), e1]
  have hv2 : v.intValuation r *
      Valued.v (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r)) ≤
      v.intValuation r := by
    have h3 := hv
    rw [← e2, Valuation.map_mul, valR_lemma_2] at h3
    exact h3
  have hne : v.intValuation r ≠ 0 := by
    first
    | exact v.intValuation_ne_zero r hr
    | exact IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v r hr
    | (rw [← valR_lemma_2 (K := K) v r, Valuation.ne_zero_iff, map_ne_zero]; exact hrK)
  calc Valued.v (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r))
      = (v.intValuation r)⁻¹ * (v.intValuation r *
          Valued.v (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ (v.intValuation r)⁻¹ * v.intValuation r := by
        first
        | gcongr
        | exact mul_le_mul_left' hv2 _
        | exact mul_le_mul_left hv2 _
    _ = 1 := inv_mul_cancel₀ hne

theorem isInt_zero : IsInt (0 : FiniteAdeleRing R K) := by
  intro v
  first
  | exact zero_mem _
  | simp
  | (show (0 : v.adicCompletion K) ∈ _; exact zero_mem _)

theorem isInt_add {a b : FiniteAdeleRing R K} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  intro v
  first
  | exact add_mem (ha v) (hb v)
  | simpa using add_mem (ha v) (hb v)

theorem isInt_mul {a b : FiniteAdeleRing R K} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  intro v
  rw [mulApp_lemma_4]
  exact mul_mem (ha v) (hb v)

theorem isInt_R (r : R) : IsInt (algebraMap R (FiniteAdeleRing R K) r) := by
  intro v
  rw [algApp_lemma_5]
  exact int_R v r

theorem mem_of_isInt (k : K) (h : IsInt (algebraMap K (FiniteAdeleRing R K) k)) :
    k ∈ (algebraMap R K).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K k (fun v => ?_)
  have h1 := h v
  rw [algKApp_lemma_6, memO_lemma] at h1
  first
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k).symm.le.trans h1
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) v k).symm.le.trans h1
  | (rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1)
  | (erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1; exact h1)
  | simpa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using h1

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
