import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.AdLat

variable {F : Type} [Field F] [NumberField F]

theorem valued_natCast_eq (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) = v.intValuation (N : 𝓞 F) := by
  have h : (N : v.adicCompletion F)
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (N : 𝓞 F)) := by simp
  rw [h, ← v.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) ≤ 1 := by
  rw [valued_natCast_eq]; exact v.intValuation_le_one _

theorem valued_natCast_ne_zero (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    Valued.v (N : v.adicCompletion F) ≠ 0 := by
  rw [valued_natCast_eq]
  exact v.intValuation_ne_zero _ (by exact_mod_cast hN.ne')

theorem exists_nat_valued_pow_le (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, Valued.v ((p ^ n : ℕ) : v.adicCompletion F) ≤ exp (-(n : ℤ)) := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, fun n => ?_⟩
  · exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · rw [valued_natCast_eq, HeightOneSpectrum.intValuation_le_pow_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) n

theorem eq_zero_of_valued_le_natCast (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F)
    (h : ∀ N : ℕ, 0 < N → Valued.v y ≤ Valued.v (N : v.adicCompletion F)) : y = 0 := by
  by_contra hy
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (γ := Valued.v y) (by simpa using hy)
  exact absurd ((h _ (pow_pos hp n)).trans (hpn n)) (not_le.2 hn)

theorem exists_limit_of_compatible (v : HeightOneSpectrum (𝓞 F)) (x : ℕ → v.adicCompletion F)
    (h : ∀ N m : ℕ, 0 < N → 0 < m →
      Valued.v (x (N * m) - x N) ≤ Valued.v (N : v.adicCompletion F)) :
    ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
      Valued.v (t - x N) ≤ Valued.v (N : v.adicCompletion F) := by
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit (K := F) v (fun n => x (p ^ n)) (fun m n hnm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add]
    exact (h _ _ (pow_pos hp n) (pow_pos hp k)).trans (hpn n))
  refine ⟨t, fun N hN => ?_⟩
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (valued_natCast_ne_zero v hN)
  have h1 := (ht n).trans hn.le
  have h2 := ((h _ _ (pow_pos hp n) hN).trans (hpn n)).trans hn.le
  have h3 := h _ _ hN (pow_pos hp n)
  have e : t - x N = (t - x (p ^ n)) - (x (p ^ n * N) - x (p ^ n)) + (x (N * p ^ n) - x N) := by
    rw [mul_comm N]; ring
  rw [e]
  exact Valuation.map_add_le _ (Valuation.map_sub_le _ h1 h2) h3

theorem valued_nsmul_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : a v ∈ v.adicCompletionIntegers F) :
    Valued.v ((N • a) v) ≤ Valued.v (N : v.adicCompletion F) := by
  have : (N • a) v = N • a v := rfl
  rw [this, nsmul_eq_mul, map_mul]
  exact mul_le_of_le_one_right' ha

theorem integral_finiteAdele_complete_separated :
    ∀ (F : Type) [Field F] [NumberField F], (∀ y : FiniteAdeleRing (𝓞 F) F, (∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = N • a) → y = 0) ∧ ∀ x : ℕ → FiniteAdeleRing (𝓞 F) F, (∀ N v, x N v ∈ v.adicCompletionIntegers F) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x (N * m) = x N + N • a) → ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = x N + N • a := by
  intro F _ _
  refine ⟨fun y hy => ?_, fun x hx h => ?_⟩
  · refine DFunLike.ext _ _ fun v => ?_
    refine eq_zero_of_valued_le_natCast v (y v) fun N hN => ?_
    obtain ⟨a, ha, rfl⟩ := hy N hN
    exact valued_nsmul_le v N a (ha v)
  · have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
        Valued.v (t - x N v) ≤ Valued.v (N : v.adicCompletion F) := fun v => by
      refine exists_limit_of_compatible v (fun N => x N v) fun N m hN hm => ?_
      obtain ⟨a, ha, e⟩ := h N m hN hm
      have : x (N * m) v - x N v = (N • a) v := by
        rw [e]
        exact add_sub_cancel_left (x N v) ((N • a) v)
      rw [this]
      exact valued_nsmul_le v N a (ha v)
    choose t ht using key
    have ht1 : ∀ v, t v ∈ v.adicCompletionIntegers F := fun v => by
      have h1 : Valued.v (t v - x 1 v) ≤ 1 := (ht v 1 one_pos).trans (valued_natCast_le_one v 1)
      have h2 : t v - x 1 v ∈ v.adicCompletionIntegers F := h1
      simpa using add_mem h2 (hx 1 v)
    refine ⟨⟨t, Filter.Eventually.of_forall ht1⟩, fun N hN => ?_⟩
    have hq : ∀ v, (t v - x N v) / (N : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
      fun v => by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ (ht v N hN) zero_le'
    refine ⟨⟨fun v => (t v - x N v) / (N : v.adicCompletion F),
      Filter.Eventually.of_forall hq⟩, hq, ?_⟩
    refine DFunLike.ext _ _ fun v => ?_
    change t v = x N v + N • ((t v - x N v) / (N : v.adicCompletion F))
    have hN0 : (N : v.adicCompletion F) ≠ 0 := fun h0 =>
      valued_natCast_ne_zero v hN (by rw [h0, map_zero])
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hN0]
    ring

end GlobalTheory.AdLat
