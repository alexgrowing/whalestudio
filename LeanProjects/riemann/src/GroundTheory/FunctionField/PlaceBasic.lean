import Mathlib
import GroundTheory.FunctionField.PlaceDefs

namespace GroundTheory.FunctionField

open Polynomial

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem mem_ring_of_isIntegral (v : Place k K) {x : K} (hx : IsIntegral k x) : x ∈ v.ring := by
  have hx' : IsIntegral v.ring x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  rw [← hy]
  exact y.2

theorem mem_ring_of_isAlgebraic (v : Place k K) {x : K} (hx : IsAlgebraic k x) : x ∈ v.ring :=
  v.mem_ring_of_isIntegral hx.isIntegral

theorem valuation_eq_one_of_isAlgebraic (v : Place k K) {x : K} (hx : IsAlgebraic k x)
    (hx0 : x ≠ 0) : v.ring.valuation x = 1 := by
  have h1 := (v.ring.valuation_le_one_iff x).2 (v.mem_ring_of_isAlgebraic hx)
  have h2 := (v.ring.valuation_le_one_iff x⁻¹).2
    (v.mem_ring_of_isAlgebraic (IsAlgebraic.inv_iff.2 hx))
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at h2
  exact le_antisymm h1 h2

theorem ord_eq_zero_of_isAlgebraic [IsFunctionField k K] (v : Place k K) {x : K}
    (hx : IsAlgebraic k x) (hx0 : x ≠ 0) : v.ord x = 0 := by
  have h := v.valuation_eq_one_of_isAlgebraic hx hx0
  rw [← v.valuation_isEquiv.eq_one_iff_eq_one] at h
  rw [ord, h, WithZero.log_one, neg_zero]

theorem exists_valuation_lt_one_of_transcendental {x : K} (hx : Transcendental k x) :
    ∃ v : Place k K, v.ring.valuation x < 1 := by
  let A : Subring K := (Algebra.adjoin k {x}).toSubring
  have hxA : x ∈ A := Algebra.self_mem_adjoin_singleton k x
  let I : Ideal A := Ideal.span {⟨x, hxA⟩}
  have hI : I ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    obtain ⟨y, hy⟩ := htop.exists_right_inv
    have hyA : (y : K) ∈ Algebra.adjoin k {x} := y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hyA
    obtain ⟨p, hp⟩ := hyA
    have hxy : x * (y : K) = 1 := congrArg Subtype.val hy
    apply hx
    refine ⟨X * p - 1, ?_, ?_⟩
    · intro h
      have h0 := congrArg (fun q : k[X] => q.coeff 0) h
      simp at h0
    · have hp' : aeval x p = (y : K) := hp
      rw [map_sub, map_mul, aeval_X, map_one, hp', hxy, sub_self]
  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hxB : x ∈ B.nonunits := hIB ⟨⟨x, hxA⟩, Ideal.subset_span rfl, rfl⟩
  refine ⟨⟨B, ?_, ?_⟩, B.mem_nonunits_iff.1 hxB⟩
  · intro htop
    rcases B.mem_nonunits_iff_or.1 hxB with h | h
    · exact hx (h ▸ isAlgebraic_zero)
    · exact h (htop ▸ ValuationSubring.mem_top x⁻¹)
  · intro c
    exact hAB (Subalgebra.algebraMap_mem (Algebra.adjoin k {x}) c)

theorem exists_not_mem_of_transcendental {x : K} (hx : Transcendental k x) :
    ∃ v : Place k K, x ∉ v.ring := by
  have hx' : Transcendental k x⁻¹ := fun h => hx (by simpa using IsAlgebraic.inv_iff.2 h)
  obtain ⟨v, hv⟩ := exists_valuation_lt_one_of_transcendental hx'
  refine ⟨v, fun hmem => ?_⟩
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have h1 := (v.ring.valuation_le_one_iff x).2 hmem
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at hv
  exact absurd h1 (not_le.2 hv)

theorem isAlgebraic_iff_forall_mem {x : K} : IsAlgebraic k x ↔ ∀ v : Place k K, x ∈ v.ring := by
  refine ⟨fun hx v => v.mem_ring_of_isAlgebraic hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨v, hv⟩ := exists_not_mem_of_transcendental hx
  exact hv (h v)

theorem nonempty [IsFunctionField k K] : Nonempty (Place k K) := by
  obtain ⟨x, hx, -⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  obtain ⟨v, -⟩ := exists_valuation_lt_one_of_transcendental hx
  exact ⟨v⟩

theorem eq_of_le [IsFunctionField k K] {v w : Place k K} (h : v.ring ≤ w.ring) : v = w := by
  ext1
  have key : ∀ (P : Ideal v.ring) [P.IsPrime], v.ring.ofPrime P = w.ring → v.ring = w.ring := by
    intro P hP hPw
    rcases eq_or_ne P ⊥ with h0 | h0
    · subst h0
      rw [ValuationSubring.ofPrime_bot] at hPw
      exact absurd hPw.symm w.ne_top
    · have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal hP h0
      have hm := IsLocalRing.eq_maximalIdeal hmax
      subst hm
      rw [ValuationSubring.ofPrime_top] at hPw
      exact hPw
  exact key _ (v.ring.ofPrime_idealOfLE w.ring h)

noncomputable def algebraicClosureToResidueField (v : Place k K) :
    algebraicClosure k K →ₐ[k] v.ResidueField where
  toRingHom := (IsLocalRing.residue v.ring).comp
    (RingHom.codRestrict ((algebraicClosure k K).val : algebraicClosure k K →+* K) v.ring
      fun y => show (y : K) ∈ v.ring from v.mem_ring_of_isAlgebraic (mem_algebraicClosure_iff.1 y.2))
  commutes' _ := rfl

theorem algebraicClosureToResidueField_injective (v : Place k K) :
    Function.Injective v.algebraicClosureToResidueField :=
  v.algebraicClosureToResidueField.toRingHom.injective

instance [IsFunctionField k K] : FiniteDimensional k (algebraicClosure k K) := by
  obtain ⟨v⟩ := Place.nonempty (k := k) (K := K)
  exact FiniteDimensional.of_injective v.algebraicClosureToResidueField.toLinearMap
    v.algebraicClosureToResidueField_injective

end Place

end GroundTheory.FunctionField
