import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.UpIdeleMod

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

omit [NumberField K] in

theorem valued_algebraMap {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.adicCompletion.valued_coe K v k

theorem valued_finiteCompletionMap (w : HeightOneSpectrum (𝓞 E)) (x : (w.under (𝓞 K)).adicCompletion K) :
    Valued.v (finiteCompletionMap K E w x) =
      Valued.v x ^ ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal) := by
  have he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, zero_pow he]
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K (w.under (𝓞 K))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set m := WithZero.log (Valued.v x)
  set k : K := π ^ (-m)
  have hvk : (w.under (𝓞 K)).valuation K k = Valued.v x := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, neg_mul_neg, mul_one]
    exact WithZero.exp_log hx0
  set c : (w.under (𝓞 K)).adicCompletion K := algebraMap K _ k
  have hc : Valued.v c = Valued.v x := (valued_algebraMap (w.under (𝓞 K)) k).trans hvk
  have hc0 : c ≠ 0 := fun h => hx0 (by rw [← hc, h, map_zero])
  set u := x * c⁻¹
  have hu0 : u ≠ 0 := mul_ne_zero hx (inv_ne_zero hc0)
  have hu : Valued.v u = 1 := by
    rw [map_mul, map_inv₀, hc, mul_inv_cancel₀ hx0]
  have hu1 : u ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have hu2 : u⁻¹ ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have a1 := finiteCompletionMap_mapsTo K E w hu1
  have a2 := finiteCompletionMap_mapsTo K E w hu2
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at a1 a2
  have hfu : Valued.v (finiteCompletionMap K E w u) = 1 := by
    have hprod : finiteCompletionMap K E w u * finiteCompletionMap K E w u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have h3 := congrArg Valued.v hprod
    rw [map_mul, map_one] at h3
    exact eq_one_of_one_le_mul_left a1 a2 h3.ge
  have hxu : x = u * c := by
    simp only [u, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  conv_lhs => rw [hxu, map_mul, map_mul, hfu, one_mul, finiteCompletionMap_coe, valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 K)) w k, hvk]

theorem factor_upIdele (t : (Af K)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((upIdele K E t : Af E) w)) =
      (((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : ℝ) ^
          WithZero.log (Valued.v ((t : Af K) (w.under (𝓞 K))))) ^
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  haveI := w.isMaximal
  haveI := (w.under (𝓞 K)).isMaximal
  have h1 : ((upIdele K E t : Af E) w) = finiteCompletionMap K E w ((t : Af K) (w.under (𝓞 K))) := rfl
  rw [h1, valued_finiteCompletionMap, WithZero.log_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 K)).asIdeal (w.under (𝓞 K)).isPrime
      (w.under (𝓞 K)).ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

open Classical in

theorem sum_fiber (v : HeightOneSpectrum (𝓞 K)) (s : Finset (HeightOneSpectrum (𝓞 E)))
    (hs : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v → w ∈ s) :
    ∑ w ∈ s with w.under (𝓞 K) = v, w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) =
      Module.finrank K E := by
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E, ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine Finset.sum_bij'
    (fun w hw => (⟨w.asIdeal, w.isPrime, by
      rw [← (Finset.mem_filter.mp hw).2]
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under K E w⟩ : v.asIdeal.primesOver (𝓞 E)))
    (fun q _ => (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)))
    (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hq : (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 K) = v :=
    HeightOneSpectrum.ext q.2.2.over.symm
  exact Finset.mem_filter.mpr ⟨hs _ hq, hq⟩

theorem modF_upIdele (t : (Af K)ˣ) : modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  classical
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((t : Af K) v)) with ha
  have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}.Finite :=
    Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp t.isUnit).2
  have hT : ((fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 K)) ⁻¹'
      {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}).Finite := by
    have h2 := Filter.mem_cofinite.mp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K E hfin.compl_mem_cofinite)
    rwa [Set.preimage_compl, compl_compl] at h2
  set S := hfin.toFinset
  set T := hT.toFinset
  have haS : ∀ v, v ∉ S → a v = 1 := fun v hv => by
    have h3 : Valued.v ((t : Af K) v) = 1 := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr h)
    simp only [ha, h3, WithZero.log_one, zpow_zero]
  have h1 : modF t = ∏ v ∈ S, a v := by
    refine finprod_eq_prod_of_mulSupport_subset a fun v hv => ?_
    by_contra h
    exact hv (haS v h)
  have h2 : modF (upIdele K E t) = ∏ w ∈ T, a (w.under (𝓞 K)) ^
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
    unfold modF
    rw [finprod_congr (factor_upIdele t)]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    by_contra h
    apply hw
    have h4 : w.under (𝓞 K) ∉ S := fun h5 => h (hT.mem_toFinset.mpr (hfin.mem_toFinset.mp h5))
    show a (w.under (𝓞 K)) ^ _ = 1
    rw [haS _ h4, one_pow]
  rw [h2, h1, ← Finset.prod_fiberwise_of_maps_to (s := T) (t := S) (g := fun w => w.under (𝓞 K))
    (fun w hw => hfin.mem_toFinset.mpr (hT.mem_toFinset.mp hw)), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Finset.prod_congr rfl (g := fun w => a v ^ (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)))
      (fun w hw => by rw [(Finset.mem_filter.mp hw).2]),
    Finset.prod_pow_eq_pow_sum, sum_fiber v T fun w hw => hT.mem_toFinset.mpr (by
      show w.under (𝓞 K) ∈ {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}
      rw [hw]; exact hfin.mem_toFinset.mp hv)]

end GlobalTheory.UpIdeleMod
