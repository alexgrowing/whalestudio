import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem rat_mem_adicInt_iff (v : HeightOneSpectrum ℤ) (q : ℚ) :
    algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
  rw [← this]
  rfl

theorem valuation_int_eq_one (v : HeightOneSpectrum ℤ) {s : ℤ} (hs : s ∉ v.asIdeal) :
    v.valuation ℚ (s : ℚ) = 1 := by
  have e : ((s : ℚ)) = algebraMap ℤ ℚ s := rfl
  rw [e]
  refine le_antisymm (v.valuation_le_one s) (not_lt.1 fun h => hs ?_)
  exact (Ideal.dvd_span_singleton).1 ((v.valuation_lt_one_iff_dvd s).1 h)

theorem den_not_mem (v : HeightOneSpectrum ℤ) (q : ℚ) (hq : v.valuation ℚ q ≤ 1) :
    ((q.den : ℤ)) ∉ v.asIdeal := by
  intro hd
  have hlt : v.valuation ℚ ((q.den : ℤ) : ℚ) < 1 := by
    have e : (((q.den : ℤ)) : ℚ) = algebraMap ℤ ℚ (q.den : ℤ) := rfl
    rw [e]; exact (v.valuation_lt_one_iff_dvd _).2 (Ideal.dvd_span_singleton.2 hd)
  have hn : v.valuation ℚ ((q.num : ℤ) : ℚ) < 1 := by
    have e : ((q.num : ℤ) : ℚ) = q * ((q.den : ℤ) : ℚ) := by
      rw [Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hq) hlt
  have hnm : q.num ∈ v.asIdeal := by
    have e : ((q.num : ℤ) : ℚ) = algebraMap ℤ ℚ q.num := rfl
    rw [e] at hn
    exact Ideal.dvd_span_singleton.1 ((v.valuation_lt_one_iff_dvd _).1 hn)
  have hc : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using q.reduced
  obtain ⟨u, w, h⟩ := hc
  have h1 : (1 : ℤ) ∈ v.asIdeal := h ▸ add_mem (Ideal.mul_mem_left _ _ hnm) (Ideal.mul_mem_left _ _ hd)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem repr_via {K M ι κ : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] (c : Module.Basis κ K M)
    (d : Module.Basis ι K M) (z : M) (i : κ) :
    c.repr z i = ∑ j, d.repr z j * c.repr (d j) i := by
  conv_lhs => rw [← d.sum_repr z]
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem isIntB_one_tmul_iff (v : HeightOneSpectrum ℤ) {L κ : Type} [Field L] [Algebra ℚ L]
    (ℓ : Module.Basis κ ℚ L) (z : L) :
    IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∀ i, v.valuation ℚ (ℓ.repr z i) ≤ 1 := by
  unfold IsIntB
  simp only [repr_tmul_apply, one_mul, rat_mem_adicInt_iff]

theorem isIntB_one_tmul_iff_exists_isIntegral : ∀ (L : Type) [Field L] [NumberField L] (κ : Type)
    (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ z : L,
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * z) := by
  intro L _ _ κ ℓ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  set b := integralBasis L
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × Module.Free.ChooseBasisIndex ℤ (𝓞 L),
      algebraMap ℚ (v.adicCompletion ℚ) (ℓ.repr (b t.2) t.1) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Module.Free.ChooseBasisIndex ℤ (𝓞 L) × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (ℓ t.2) t.1) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv z => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨h1v, h2v⟩ := hv
  simp only [rat_mem_adicInt_iff] at h1v h2v
  rw [isIntB_one_tmul_iff]
  constructor
  · intro hz
    have hb : ∀ j, v.valuation ℚ (b.repr z j) ≤ 1 := fun j => by
      rw [repr_via b ℓ z j]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      exact mul_le_one' (hz i) (h2v (j, i))
    refine ⟨∏ j, ((b.repr z j).den : ℤ), ?_, ?_⟩
    · intro hd
      obtain ⟨j, _, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hd
      exact den_not_mem v _ (hb j) hj
    · set d : ℤ := ∏ j, ((b.repr z j).den : ℤ) with hd
      have hdv : ∀ j, ((b.repr z j).den : ℤ) ∣ d := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have hmem : (d : L) * z ∈ Submodule.span ℤ (Set.range b) := by
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨fun j => d / ((b.repr z j).den : ℤ) * (b.repr z j).num, ?_⟩
        conv_rhs => rw [← b.sum_repr z]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hc : (((d / ((b.repr z j).den : ℤ) * (b.repr z j).num : ℤ)) : ℚ) = (d : ℚ) * b.repr z j := by
          have e1 := Int.ediv_mul_cancel (hdv j)
          conv_rhs => rw [← e1]
          rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, mul_comm ((b.repr z j).den : ℚ),
            Rat.mul_den_eq_num]
        rw [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, hc, mul_smul]
      obtain ⟨y, hy⟩ := (mem_span_integralBasis L).1 hmem
      rw [← hy]
      exact RingOfIntegers.isIntegral_coe y
  · rintro ⟨s, hs, hint⟩ i
    have hmem : (s : L) * z ∈ Submodule.span ℤ (Set.range b) := (mem_span_integralBasis L).2 ⟨⟨_, hint⟩, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
    have hsz : ℓ.repr ((s : L) * z) i = (s : ℚ) * ℓ.repr z i := by
      rw [← zsmul_eq_mul, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
    have hval : v.valuation ℚ (ℓ.repr ((s : L) * z) i) ≤ 1 := by
      rw [← hc, map_sum, Finsupp.finset_sum_apply]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, map_mul]
      have e : ((c j : ℤ) : ℚ) = algebraMap ℤ ℚ (c j) := rfl
      rw [e]
      exact mul_le_one' (v.valuation_le_one (c j)) (h1v (i, j))
    rwa [hsz, map_mul, valuation_int_eq_one v hs, one_mul] at hval

end GlobalTheory.AdicSpan
