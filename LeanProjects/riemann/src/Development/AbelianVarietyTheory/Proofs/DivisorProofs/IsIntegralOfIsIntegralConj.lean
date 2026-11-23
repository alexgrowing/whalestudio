import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem exists_finset_algebraMap_mem (s : Finset ℚ) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ q ∈ s,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  let d : ℤ := ∏ q ∈ s, (q.den : ℤ)
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ => by exact_mod_cast q.den_nz
  have hfin : {v : HeightOneSpectrum ℤ | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hd)
  refine ⟨hfin.toFinset, fun v hv q hq => ?_⟩
  have hden : (q.den : ℤ) ∉ v.asIdeal := by
    intro h
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hq) h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
  rw [e]
  have hq' : q = ((q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) := by
    push_cast; exact (Rat.num_div_den q).symm
  rw [hq', map_div₀]
  have h1 : v.valuation ℚ ((q.num : ℤ) : ℚ) ≤ 1 := by
    rw [show ((q.num : ℤ) : ℚ) = algebraMap ℤ ℚ q.num from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one _
  have h2 : v.valuation ℚ ((q.den : ℤ) : ℚ) = 1 := by
    rw [show ((q.den : ℤ) : ℚ) = algebraMap ℤ ℚ q.den from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one _)
      (not_lt.1 fun h => hden ((v.intValuation_lt_one_iff_mem _).1 h))
  rw [h2, div_one]
  exact h1

theorem isIntegral_of_isIntegral_conj {R A : Type} [CommRing R] [Ring A] [Algebra R A] (X : Aˣ) (y : A)
    (h : IsIntegral R (↑X * y * ↑X⁻¹)) : IsIntegral R y := by
  let f : A →ₐ[R] A :=
    { toFun := fun z => ↑X⁻¹ * z * ↑X
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show _ * _ * _ = _
        rw [mul_assoc, Algebra.commutes, Units.inv_mul_cancel_left] }
  have := h.map f
  simpa [f, mul_assoc] using this

theorem map_id_injective (K : Type) [CommRing K] [Algebra ℚ K] {L C : Type} [Ring L] [Algebra ℚ L] [Ring C]
    [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (hι : Function.Injective ι) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hι

theorem mem_of_isIntegral (v : HeightOneSpectrum ℤ) {x : v.adicCompletion ℚ}
    (hx : IsIntegral (v.adicCompletionIntegers ℚ) x) : x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact y.2

theorem trace_one_tmul' {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

end GlobalTheory.LocIntSpan
