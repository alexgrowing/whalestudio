import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplit

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.HatPlace

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral : IsOpen {y : Af E | ∀ w, Valued.v (y w) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => v.adicCompletionIntegers E) fun _ => Valued.isOpen_valuationSubring _

theorem exists_approx {S : Set (Af E)} {z : Af E} (hz : z ∈ closure S) {n : OF E} (hn : n ≠ 0) :
    ∃ x ∈ S, ∃ y : Af E, (∀ w, Valued.v (y w) ≤ 1) ∧ z = x + iota n * y := by
  have hn0 : algebraMap (OF E) E n ≠ 0 := fun h => hn (Subtype.ext (Subtype.ext h))
  have ho : IsOpen ((fun t : Af E => algebraMap E (Af E) (algebraMap (OF E) E n)⁻¹ * (z - t)) ⁻¹'
      {y : Af E | ∀ w, Valued.v (y w) ≤ 1}) :=
    isOpen_integral.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  obtain ⟨x, hx, hxS⟩ := mem_closure_iff.1 hz _ ho (fun w => by
    simp only [sub_self, mul_zero, zero_coord, map_zero, zero_le'])
  refine ⟨x, hxS, _, hx, ?_⟩
  rw [iota, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, add_sub_cancel]

theorem mem_iff_val {J : Ideal (𝓞 E)} (hJ : J ≠ ⊥) (b : 𝓞 E) :
    b ∈ J ↔ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal J : ℤ)) := by
  conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hJ, Ideal.mem_iInf]
  refine forall_congr' fun P => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hJ, ← P.intValuation_le_pow_iff_mem,
    ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]

theorem val_mul_le {c : Ideal (OF E)} (hc : c ≠ ⊥) {n : OF E} (hn : n ∈ c) {y : Af E} (hy : ∀ w, Valued.v (y w) ≤ 1)
    (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((iota n * y) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  rw [mul_coord, map_mul]
  exact (mul_le_mul' ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 (Ideal.mem_map_of_mem _ hn) w)
    (hy w)).trans_eq (mul_one _)

theorem mem_hatO_of_val {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) : z ∈ hatO c := by
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz P).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hx : x ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc)]
    intro P
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E x) = z - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [hxy, add_sub_cancel_right]
    rw [h1, sub_coord]
    exact Valuation.map_sub_le _ (hz P) (val_mul_le hc (Ideal.absNorm_mem c) hy P)
  rw [hxy]
  exact add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨0, _, hx, by rw [map_zero, zero_add]⟩))
    (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)

theorem exists_integer {f : E} (hf : f ∈ maximalRealSubfield E)
    (h : ∀ w, Valued.v (algebraMap E (Af E) f w) ≤ 1) : ∃ a : OF E, algebraMap (OF E) E a = f := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E f fun w => by
    have := h w
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  have h1 : IsIntegral ℤ f := hb ▸ b.isIntegral_coe
  have h2 : IsIntegral ℤ (⟨f, hf⟩ : maximalRealSubfield E) :=
    (isIntegral_algebraMap_iff (A := maximalRealSubfield E) (B := E) (RingHom.injective _)).1 h1
  exact ⟨⟨_, h2⟩, rfl⟩

theorem mem_hatO_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E,
    z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)),
      Valued.v (z w - a w) ≤
        WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  intro E _ _ _ c hc z
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  constructor
  · intro hz
    obtain ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩ := exists_approx hz hn0
    obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
    refine ⟨iota a, Subring.le_topologicalClosure _ ⟨_, (a : maximalRealSubfield E).2, rfl⟩,
      fun w => val_iota_le_one w a, fun w => ?_⟩
    rw [← sub_coord, map_add, add_assoc]
    erw [add_sub_cancel_left]
    rw [add_coord]
    exact Valuation.map_add_le _ ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 hb w) (val_mul_le hc hn hy w)
  · rintro ⟨a, ha, hai, hz⟩
    obtain ⟨_, ⟨f, hf, rfl⟩, y, hy, rfl⟩ := exists_approx ha hn0
    obtain ⟨a, rfl⟩ := exists_integer hf fun w => by
      have h1 : Valued.v ((iota n * y) w) ≤ 1 := by
        rw [mul_coord, map_mul]; exact mul_le_one' (val_iota_le_one w n) (hy w)
      have h2 := Valuation.map_sub_le _ (hai w) h1
      rwa [add_coord, add_sub_cancel_right] at h2
    have h1 : z - (algebraMap E (Af E) (algebraMap (OF E) E a) + iota n * y) ∈ hatO c := mem_hatO_of_val hc hz
    have h2 := add_mem h1 (add_mem (algebraMap_mem_hatO (algebraMap_mem_orderC c a)) (PicFin.mul_mem_hatO hn hy))
    exact sub_add_cancel z _ ▸ h2

end GlobalTheory.CMVal.HatPlace
