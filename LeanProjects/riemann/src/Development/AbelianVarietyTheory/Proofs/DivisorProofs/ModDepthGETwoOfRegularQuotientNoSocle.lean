import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem modDepthGE_two_of_isSMulRegular_of_quotSMulTop :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M]
      [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S →
      IsSMulRegular M x →
      (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) →
        u ∈ x • (⊤ : Submodule S M)) →
      ReciprocityTheory.CA.ModDepthGE S M 2 := by
  intro S _ _ _ M _ _ _ _ x hxm hreg hsoc
  obtain ⟨y, hym, hyreg⟩ : ∃ y ∈ maximalIdeal S, IsSMulRegular (QuotSMulTop x M) y := by
    by_contra hno
    push_neg at hno
    have hfin := associatedPrimes.finite S (QuotSMulTop x M)
    have hsub : (maximalIdeal S : Set S) ⊆
        ⋃ p ∈ associatedPrimes S (QuotSMulTop x M), (p : Set S) := by
      intro y hy
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hno y hy
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun p hp _ _ => (hfin.mem_toFinset.mp hp).isPrime)).mp (by simpa using hsub)
    rw [hfin.mem_toFinset] at hp
    have hpm : p = maximalIdeal S :=
      (le_antisymm (le_maximalIdeal (hp.isPrime.ne_top)) hmp)
    rw [hpm] at hp
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hu : ∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M) := by
      intro a ha
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at ha
      exact ha
    apply (maximalIdeal.isMaximal S).ne_top
    rw [hw, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact hsoc u hu
  refine ⟨[x, y], rfl, (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption), ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption),
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact ⟨hreg, hyreg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩

end GlobalTheory
