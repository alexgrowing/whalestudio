import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModPStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

def IsPowModP {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) (p : ℕ)
    (x : A) : Prop :=
  ∃ y ∈ S, ∃ z ∈ S, x = y ^ p + (p : A) * z

section Closure

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {p : ℕ}

theorem isPthPowerModP_add (hp : p.Prime) {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x + x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨y, hy⟩ : S) ⟨y', hy'⟩
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  refine ⟨y + y', S.add_mem hy hy', z + z' - y * y' * r, ?_, ?_⟩
  · exact S.sub_mem (S.add_mem hz hz') (S.mul_mem (S.mul_mem hy hy') r.2)
  · rw [hr']; ring

theorem isPthPowerModP_mul {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x * x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  refine ⟨y * y', S.mul_mem hy hy', z * y' ^ p + y ^ p * z' + (p : A) * z * z', ?_, ?_⟩
  · refine S.add_mem (S.add_mem (S.mul_mem hz (S.pow_mem hy' _))
      (S.mul_mem (S.pow_mem hy _) hz')) (S.mul_mem (S.mul_mem ?_ hz) hz')
    exact S.natCast_mem p
  · ring

theorem isPthPowerModP_pow {y : A} (hy : y ∈ S) : IsPowModP S p (y ^ p) :=
  ⟨y, hy, 0, S.zero_mem, by ring⟩

theorem isPthPowerModP_zero (hp : p.Prime) : IsPowModP S p 0 :=
  ⟨0, S.zero_mem, 0, S.zero_mem, by rw [zero_pow hp.ne_zero]; ring⟩

theorem isPthPowerModP_add_p_mul {x h : A} (hx : IsPowModP S p x) (hh : h ∈ S) :
    IsPowModP S p (x + (p : A) * h) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y, hy, z + h, S.add_mem hz hh, by ring⟩

end Closure

theorem frob_surj_adjoin_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  intro p hp Ω _ _ T x hx
  set S := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) with hS
  have hpp : p.Prime := hp.out
  have hζ : ∀ n, T.ζ n ∈ S := fun n => Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hq : ∀ n, T.qq n ∈ S := fun n => Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  suffices IsPowModP S p x from this
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [← T.ζpow n]; exact isPthPowerModP_pow S (hζ _)
    · rw [← T.qpow n]; exact isPthPowerModP_pow S (hq _)
  | algebraMap r =>
    obtain ⟨g, h, rfl⟩ := GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p p r
    rw [map_add, map_sum, map_mul, map_natCast]
    refine isPthPowerModP_add_p_mul S ?_ ?_
    · refine Finset.sum_induction _ (IsPowModP S p) (fun a b ha hb => isPthPowerModP_add S hpp ha hb)
        (isPthPowerModP_zero S hpp) ?_
      intro j _
      have e : algebraMap (O0 p) Ω (qO p ^ (j : ℕ) * g j ^ p) =
          (T.qq 1 ^ (j : ℕ) * algebraMap (O0 p) Ω (g j)) ^ p := by
        rw [map_mul, map_pow, map_pow, ← T.q0, ← T.qpow 0, mul_pow, ← pow_mul, ← pow_mul, mul_comm p]
      rw [e]
      exact isPthPowerModP_pow S (S.mul_mem (S.pow_mem (hq 1) _) (S.algebraMap_mem _))
    · exact S.algebraMap_mem _
  | add x y _ _ hx hy => exact isPthPowerModP_add S hpp hx hy
  | mul x y _ _ hx hy => exact isPthPowerModP_mul S hx hy

end GlobalTheory.K5
