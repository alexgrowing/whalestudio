import Mathlib

noncomputable section

open IsDedekindDomain WithZero

namespace ReciprocityTheory.UG.AdeleIntA

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def IsInt (y : FiniteAdeleRing R K) : Prop := ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K

theorem isInt_zero : IsInt (0 : FiniteAdeleRing R K) := fun v => zero_mem (v.adicCompletionIntegers K)

theorem isInt_add {x y : FiniteAdeleRing R K} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) :=
  fun v => add_mem (hx v) (hy v)

theorem isInt_mul {x y : FiniteAdeleRing R K} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) :=
  fun v => mul_mem (hx v) (hy v)

theorem val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  have h := v.valuedAdicCompletion_eq_valuation' (algebraMap R K r)
  rw [v.valuation_of_algebraMap] at h
  exact h

theorem isInt_R (r : R) : IsInt (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) := by
  intro v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1
  rw [val_R]
  exact v.intValuation_le_one r

theorem val_le_one_of_mem {v : HeightOneSpectrum R} {x : v.adicCompletion K} (h : x ∈ v.adicCompletionIntegers K) :
    Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers R K v).1 h

theorem local_approx (v : HeightOneSpectrum R) (x : v.adicCompletion K) (hx : Valued.v x ≤ 1) (m : R) (hm : m ≠ 0) :
    ∃ a : R, Valued.v (x - algebraMap K (v.adicCompletion K) (algebraMap R K a)) < v.intValuation m := by
  have hm0 : v.intValuation m ≠ 0 := v.intValuation_ne_zero m hm
  set γ : (ℤᵐ⁰)ˣ := Units.mk0 _ hm0
  set M : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K m)
  have hM : Valued.v M = v.intValuation m := val_R v m
  have hMne : M ≠ 0 := fun h => hm0 (by rw [← hM, h, map_zero])
  have hM0 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict M ≠ 0 := by
    simpa using hMne
  have hball : {z : v.adicCompletion K | Valued.v (z - x) < Valued.v M} ∈ nhds x :=
    (Valued.mem_nhds).2 ⟨Units.mk0 _ hM0, fun z hz => by
      simpa using (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict_lt_iff.mp hz⟩
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := K) v).mem_nhds hball
  have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - x) < v.intValuation m := hM ▸ hk
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have e : (k : v.adicCompletion K) = (algebraMap K (v.adicCompletion K) k - x) + x := by
      rw [sub_add_cancel]; rfl
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ hx)
    exact hk'.le.trans (v.intValuation_le_one m)
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := K) v hk1 γ
  refine ⟨a, ?_⟩
  have e : x - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      -(algebraMap K (v.adicCompletion K) k - x) - algebraMap K (v.adicCompletion K) (algebraMap R K a - k) := by
    rw [map_sub]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_neg]; exact hk'
  · have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (algebraMap R K a - k)
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a - k)) = _ at this
    rw [this]
    exact ha

theorem exists_approx (y : FiniteAdeleRing R K) (hy : ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K)
    (m : R) (hm : m ≠ 0) : ∃ a : R, ∀ v : HeightOneSpectrum R,
      Valued.v (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) ≤ v.intValuation m := by
  classical
  have hfin : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {m}}.Finite := by
    have hne : Ideal.span {m} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
    have := Ideal.finite_factors hne
    exact this
  set S := hfin.toFinset
  choose b hb using fun v : HeightOneSpectrum R => local_approx v (y v) (val_le_one_of_mem (hy v)) m hm
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {m})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => b v)
  refine ⟨a, fun v => ?_⟩
  have hloc := hb v
  by_cases hv : v ∈ S
  · have h1 := ha v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← v.intValuation_eq_exp_neg_multiplicity hm] at h1
    have e : y v - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
        (y v - algebraMap K (v.adicCompletion K) (algebraMap R K (b v))) -
          algebraMap K (v.adicCompletion K) (algebraMap R K (a - b v)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le hloc.le ?_)
    rw [val_R]
    exact h1
  · have hv1 : v.intValuation m = 1 := by
      rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
      intro hmem
      apply hv
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
    rw [hv1]
    refine (Valuation.map_sub _ _ _).trans (max_le (val_le_one_of_mem (hy v)) ?_)
    rw [val_R]
    exact v.intValuation_le_one a

theorem exists_approx_adele (α : FiniteAdeleRing R K) : ∃ u : K, IsInt (α - algebraMap K (FiniteAdeleRing R K) u) := by
  classical
  have hT : {v : HeightOneSpectrum R | α v ∉ v.adicCompletionIntegers K}.Finite := by
    have := α.2
    rw [Filter.eventually_cofinite] at this
    exact this
  set T := hT.toFinset
  have hden : ∀ v : HeightOneSpectrum R, ∃ d : R, d ≠ 0 ∧ Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d) * α v) ≤ 1 := by
    intro v
    by_cases h0 : α v = 0
    · exact ⟨1, one_ne_zero, by simp [h0]⟩
    have hα0 : Valued.v (α v) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨n, hn⟩ : ∃ n : ℕ, exp (-(n : ℤ)) * Valued.v (α v) ≤ 1 := by
      obtain ⟨z, hz⟩ : ∃ z : ℤ, Valued.v (α v) = exp z := ⟨log (Valued.v (α v)), (exp_log hα0).symm⟩
      refine ⟨z.toNat, ?_⟩
      rw [hz, ← exp_add, ← exp_zero, exp_le_exp]
      omega
    obtain ⟨d, hd, hd0⟩ : ∃ d ∈ v.asIdeal ^ n, d ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero n v.ne_bot)
    refine ⟨d, hd0, ?_⟩
    rw [Valuation.map_mul, val_R]
    exact (mul_le_mul' ((HeightOneSpectrum.intValuation_le_pow_iff_mem v d n).2 hd) le_rfl).trans hn
  choose dv hdv0 hdv using hden
  set d : R := ∏ v ∈ T, dv v
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hdv0 v
  have hdK : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd0
  set y : FiniteAdeleRing R K := algebraMap K (FiniteAdeleRing R K) (algebraMap R K d) * α
  have hy : ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K := by
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d) * α v) ≤ 1
    by_cases hv : v ∈ T
    · have e : d = dv v * ∏ w ∈ T.erase v, dv w := (Finset.mul_prod_erase T dv hv).symm
      have h1 := hdv v
      rw [Valuation.map_mul] at h1
      rw [e]
      simp only [map_mul]
      have h2 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (∏ w ∈ T.erase v, dv w))) ≤ 1 := by
        rw [val_R]; exact v.intValuation_le_one _
      have h3 := mul_le_mul' h2 h1
      rw [one_mul] at h3
      refine le_trans (le_of_eq ?_) h3
      rw [mul_comm (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (dv v)))), mul_assoc]
    · have hαv : α v ∈ v.adicCompletionIntegers K := by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).2 h)
      rw [Valuation.map_mul, val_R]
      exact mul_le_one' (v.intValuation_le_one d) (val_le_one_of_mem hαv)
  obtain ⟨a, ha⟩ := exists_approx y hy d hd0
  refine ⟨algebraMap R K a / algebraMap R K d, fun v => ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hdv' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)) ≠ 0 := by
    rw [val_R]; exact v.intValuation_ne_zero d hd0
  have e : (α - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K d)) v =
      (algebraMap K (v.adicCompletion K) (algebraMap R K d))⁻¹ *
        (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) := by
    have hne : algebraMap K (v.adicCompletion K) (algebraMap R K d) ≠ 0 := (map_ne_zero _).2 hdK
    show α v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K d) = _
    show _ = _ * (algebraMap K (v.adicCompletion K) (algebraMap R K d) * α v - _)
    rw [map_div₀]
    field_simp
  rw [e, Valuation.map_mul, map_inv₀]
  have := ha v
  rw [← val_R (K := K)] at this
  calc (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)))⁻¹ *
        Valued.v (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a))
      ≤ (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)))⁻¹ *
        Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)) := mul_le_mul' le_rfl this
    _ = 1 := inv_mul_cancel₀ hdv'

end ReciprocityTheory.UG.AdeleIntA
