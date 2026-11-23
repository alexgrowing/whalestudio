import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.UnramCompletion

variable {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))

theorem intValuation_eq_of_notMem_sq {a : 𝓞 E} (h1 : a ∈ Q.asIdeal) (h2 : a ∉ Q.asIdeal ^ 2) :
    Q.intValuation a = exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have e1 := (Q.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)
  have e2 := mt (Q.intValuation_le_pow_iff_mem a 2).1 h2
  have h0 : Q.intValuation a ≠ 0 := Q.intValuation_ne_zero a ha
  rw [← exp_log h0] at e1 e2 ⊢
  rw [exp_le_exp] at e1 e2
  congr 1
  push_cast at e1 e2
  omega

theorem exists_eq_pow_mul {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) (k : ℕ) {x : Q.adicCompletion E}
    (hx : Valued.v x ≤ exp (-(k : ℤ))) :
    ∃ z : Q.adicCompletionIntegers E, x = (π : Q.adicCompletion E) ^ k * z := by
  have hk : Valued.v ((π : Q.adicCompletion E) ^ k) = exp (-(k : ℤ)) := by
    rw [map_pow, hπ, ← exp_nsmul]; simp
  have h0 : (π : Q.adicCompletion E) ^ k ≠ 0 := by
    intro h; rw [h, map_zero] at hk; exact exp_ne_zero hk.symm
  refine ⟨⟨x / (π : Q.adicCompletion E) ^ k, ?_⟩, (mul_div_cancel₀ _ h0).symm⟩
  rw [mem_adicCompletionIntegers, map_div₀, hk, div_le_one₀ (zero_lt_iff.2 exp_ne_zero)]
  exact hx

theorem le_exp_neg_one_of_lt_one {γ : ℤᵐ⁰} (h : γ < 1) : γ ≤ exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  rw [← exp_log h0] at h ⊢
  rw [← exp_zero, exp_lt_exp] at h
  rw [exp_le_exp]
  omega

theorem maximalIdeal_eq_span {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (Q.adicCompletionIntegers E) = Ideal.span {π} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one,
    Ideal.mem_span_singleton]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := exists_eq_pow_mul Q hπ 1 (le_exp_neg_one_of_lt_one (lt_of_le_of_ne x.2 h))
    exact ⟨z, Subtype.ext (by simpa using hz)⟩
  · rintro ⟨z, rfl⟩ h
    have hz : Valued.v (z : Q.adicCompletion E) ≤ 1 := z.2
    have : Valued.v ((π : Q.adicCompletion E) * z) ≤ exp (-1 : ℤ) := by
      rw [map_mul, hπ]; exact mul_le_of_le_one_right' hz
    have h' : Valued.v ((π : Q.adicCompletion E) * z) = 1 := h
    rw [h', ← exp_zero, exp_le_exp] at this
    omega

theorem exists_global_approx {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) (y : Q.adicCompletionIntegers E) (k : ℕ) :
    ∃ (x : 𝓞 E) (z : Q.adicCompletionIntegers E),
      algebraMap (𝓞 E) (Q.adicCompletionIntegers E) x = y + π ^ k * z := by
  obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le Q (a := (y : Q.adicCompletion E)) y.2 k
  rw [Valuation.map_sub_swap] at hs
  obtain ⟨z, hz⟩ := exists_eq_pow_mul Q hπ k hs
  refine ⟨s, z, Subtype.ext ?_⟩
  change algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) =
    (y : Q.adicCompletion E) + (π : Q.adicCompletion E) ^ k * z
  rw [← hz]; ring

theorem card_quot {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) :
    Nat.card (Q.adicCompletionIntegers E ⧸ Ideal.span {π}) = Nat.card (𝓞 E ⧸ Q.asIdeal) := by
  let f : 𝓞 E →+* Q.adicCompletionIntegers E ⧸ Ideal.span {π} :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 E) (Q.adicCompletionIntegers E))
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, z, h⟩ := exists_global_approx Q hπ y 1
    refine ⟨x, ?_⟩
    change Ideal.Quotient.mk _ _ = _
    rw [h, Ideal.Quotient.eq, add_sub_cancel_left, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hk : RingHom.ker f = Q.asIdeal := by
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ _ = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← maximalIdeal_eq_span Q hπ, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, SelfDualGenus.isUnit_algebraMap_iff, not_not]
  rw [← hk]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv).symm

theorem ringHom_ext_of_continuous {f g : Q.adicCompletion E → Q.adicCompletion E}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ k : E, f (algebraMap E _ k) = g (algebraMap E _ k)) : f = g :=
  (denseRange_algebraMap E Q).equalizer hf hg (funext h)

theorem exists_ringEquiv (c : E ≃+* E) (hc : Mem.Chr.ConjPl c Q Q) :
    ∃ σ : Q.adicCompletion E ≃+* Q.adicCompletion E, Continuous σ ∧
      (∀ k : E, σ (algebraMap E _ k) = algebraMap E _ (c k)) ∧ ∀ x, Valued.v (σ x) = Valued.v x := by
  obtain ⟨s, s1, s2, s3⟩ := Mem.Chr.exists_finCompl_map c hc
  obtain ⟨t, t1, t2, -⟩ := Mem.Chr.exists_finCompl_map c.symm ((Mem.Chr.conjPl_symm_iff c Q Q).2 hc)
  refine ⟨RingEquiv.ofRingHom s t ?_ ?_, s1, s2, s3⟩
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (s1.comp t1) continuous_id fun k => by
      simp [s2, t2])
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (t1.comp s1) continuous_id fun k => by
      simp [s2, t2])

theorem intAt_iff (x : E) : Formalism.L2.Col.IntAt Q x ↔ Q.valuation E x ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 := congrArg (Q.valuation E) h
    rw [map_mul, (valuation_eq_one_iff_notMem Q).2 hs, one_mul] at h1
    rw [h1]
    exact Q.valuation_le_one r
  · intro hx
    obtain ⟨n, d, h⟩ := Q.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

end GlobalTheory.UnramCompletion

open Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory.UnramCompletion

theorem exists_completion_frobenius : ∀ (E : Type) [Field E] [NumberField E] (p n : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → φ ^ n = 1 → ∃ (W Qq : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field Qq) (_ : Algebra W Qq) (i : E →+* Qq) (σ : Qq ≃+* Qq), IsFractionRing W Qq ∧ Irreducible (p : W) ∧ Nat.card (W ⧸ Ideal.span {(p : W)}) = Nat.card (𝓞 E ⧸ Q.asIdeal) ∧ IsAdicComplete (Ideal.span {(p : W)}) W ∧ (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) ∧ σ ^ n = 1 ∧ (∀ x : E, σ (i x) = i (φ x)) ∧ (∀ x : E, Formalism.L2.Col.IntAt Q x ↔ i x ∈ Set.range (algebraMap W Qq)) ∧ ∀ (y : W) (k : ℕ), ∃ (x : 𝓞 E) (z : W), i (x : E) = algebraMap W Qq (y + (p : W) ^ k * z) := by
  intro E _ _ p n Q φ hp h1 h2 hφ hn
  have hπ : Valued.v (((p : ℕ) : Q.adicCompletionIntegers E) : Q.adicCompletion E) = exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap (𝓞 E) (Q.adicCompletionIntegers E)),
      algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation',
      valuation_of_algebraMap]
    exact intValuation_eq_of_notMem_sq Q h1 h2
  have hc : Mem.Chr.ConjPl φ.toRingEquiv Q Q := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = φ • x := RingOfIntegers.ext hxy
    rw [e]
    constructor
    · intro hx
      simpa using Q.asIdeal.add_mem (hφ x) (Q.asIdeal.pow_mem_of_mem hx p hp.pos)
    · intro hx
      exact Q.isPrime.mem_of_pow_mem p (by simpa using Q.asIdeal.sub_mem hx (hφ x))
  obtain ⟨σ, σ1, σ2, σ3⟩ := exists_ringEquiv Q φ.toRingEquiv hc
  have hm := maximalIdeal_eq_span Q hπ
  refine ⟨Q.adicCompletionIntegers E, Q.adicCompletion E, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, algebraMap E _, σ, inferInstance, ?_, card_quot Q hπ, ?_, ?_, ?_,
    σ2, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm
  · rw [← hm]; exact SelfDualGenus.isAdicComplete_adicCompletionIntegers Q
  · intro x
    obtain ⟨a, z, ha⟩ := exists_global_approx Q hπ x 1
    have hz : σ z ∈ Q.adicCompletionIntegers E := (σ3 z).trans_le z.2
    have hx : σ x ∈ Q.adicCompletionIntegers E := (σ3 x).trans_le x.2
    have e1 : algebraMap (𝓞 E) (Q.adicCompletionIntegers E) (φ • a) =
        ⟨σ x, hx⟩ + (p : Q.adicCompletionIntegers E) * ⟨σ z, hz⟩ := by
      apply Subtype.ext
      have := congrArg (fun t : Q.adicCompletionIntegers E => σ t) ha
      simp only [pow_one] at this
      push_cast at this ⊢
      rw [map_add, map_mul, map_natCast] at this
      rw [← this]
      exact (σ2 (a : E)).symm
    have e2 : algebraMap (𝓞 E) (Q.adicCompletionIntegers E) (φ • a - a ^ p) ∈
        Ideal.span {(p : Q.adicCompletionIntegers E)} := by
      rw [← hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, SelfDualGenus.isUnit_algebraMap_iff,
        not_not]
      exact hφ a
    have e3 : (⟨σ x, hx⟩ : Q.adicCompletionIntegers E) - x ^ p ∈
        Ideal.span {(p : Q.adicCompletionIntegers E)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at e2 ⊢
      have hp0 : Ideal.Quotient.mk (Ideal.span {(p : Q.adicCompletionIntegers E)})
          (p : Q.adicCompletionIntegers E) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [map_sub (algebraMap _ _), map_pow (algebraMap _ _), e1, ha, pow_one] at e2
      simp only [map_sub, map_add, map_mul, map_pow, hp0, zero_mul, add_zero] at e2 ⊢
      exact e2
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 e3
    refine ⟨y, ?_⟩
    rw [← hy, add_sub_cancel]
    rfl
  · have key : ∀ m : ℕ, Continuous (σ ^ m : _ ≃+* _) ∧
        ∀ k : E, (σ ^ m : _ ≃+* _) (algebraMap E _ k) = algebraMap E _ ((φ ^ m) k) := by
      intro m
      induction m with
      | zero => exact ⟨continuous_id, fun k => rfl⟩
      | succ m ih =>
        rw [pow_succ', pow_succ']
        refine ⟨σ1.comp ih.1, fun k => ?_⟩
        change σ ((σ ^ m : _ ≃+* _) _) = _
        rw [ih.2, σ2]
        rfl
    refine DFunLike.coe_injective (ringHom_ext_of_continuous Q (key n).1 continuous_id fun k => ?_)
    rw [(key n).2, hn]
    rfl
  · intro x
    rw [intAt_iff, ← valuedAdicCompletion_eq_valuation' Q]
    exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨y, hy⟩ => by
      have : Valued.v (algebraMap _ (Q.adicCompletion E) y) ≤ 1 := y.2
      rwa [hy] at this⟩
  · intro y k
    obtain ⟨x, z, h⟩ := exists_global_approx Q hπ y k
    exact ⟨x, z, by rw [← h]; rfl⟩

end GlobalTheory.UnramCompletion
