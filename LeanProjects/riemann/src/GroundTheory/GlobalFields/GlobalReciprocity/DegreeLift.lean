import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.PrimesAbove

namespace GroundTheory.Global

namespace Cyclotomic

open IsDedekindDomain NumberField IntermediateField GroundTheory.LocalField.Abstract ProfiniteInteger
open scoped Pointwise GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section FiniteLevel

theorem exists_pnat_forall_dvd (t : ℤ̂) (ht : ∀ q : Nat.Primes, toPadicInt q t ≠ 0) {g : ℕ}
    (hg : 0 < g) : ∃ m : ℕ+, ∀ k : ℤ, proj m ((k : ℤ̂) * t) = 0 → (g : ℤ) ∣ k := by
  have hs : ∀ q : Nat.Primes, ∃ s : ℕ, ‖((q : ℕ) : ℤ_[q]) ^ s‖ < ‖toPadicInt q t‖ := fun q ↦ by
    have h1 : ‖((q : ℕ) : ℤ_[q])‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast q.2.one_lt)
    obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 (ht q)) h1
    exact ⟨s, by rwa [norm_pow]⟩
  choose s hs using hs
  let c : ℕ → ℕ := fun p ↦ if hp : p.Prime then p ^ s ⟨p, hp⟩ else 1
  set m : ℕ := g * ∏ p ∈ g.primeFactors, c p with hm
  have hm0 : 0 < m := Nat.mul_pos hg (Finset.prod_pos fun p _ ↦ by
    unfold c; split_ifs with hp
    · exact pow_pos hp.pos _
    · exact one_pos)
  refine ⟨⟨m, hm0⟩, fun k hk ↦ ?_⟩
  obtain ⟨z, hz⟩ := exists_eq_nsmul_of_proj_eq_zero hk
  rw [Int.natCast_dvd]
  refine (Nat.dvd_iff_prime_pow_dvd_dvd k.natAbs g).2 fun p j hp hpj ↦ ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero]; exact one_dvd _
  have hpg : p ∈ g.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p hj.ne').trans hpj, hg.ne'⟩
  set q : Nat.Primes := ⟨p, hp⟩
  have : Fact p.Prime := ⟨hp⟩

  have hq : ((k : ℤ) : ℤ_[q]) * toPadicInt q t = ((m : ℕ) : ℤ_[q]) * toPadicInt q z := by
    have := congrArg (toPadicInt q) hz
    simpa only [map_mul, map_intCast, nsmul_eq_mul, map_natCast, PNat.mk_coe] using this
  have hprod : ‖((∏ p ∈ g.primeFactors, c p : ℕ) : ℤ_[q])‖ ≤ ‖((p : ℕ) : ℤ_[q]) ^ s q‖ := by
    rw [← Finset.mul_prod_erase _ _ hpg, Nat.cast_mul, norm_mul]
    have hc : c p = p ^ s q := dif_pos hp
    rw [hc, Nat.cast_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  have hgp : ‖((g : ℕ) : ℤ_[q])‖ ≤ ‖((p ^ j : ℕ) : ℤ_[q])‖ := by
    obtain ⟨e, he⟩ := hpj
    rw [he, Nat.cast_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  have htq : 0 < ‖toPadicInt q t‖ := norm_pos_iff.2 (ht q)
  have hk : ‖((k : ℤ) : ℤ_[q])‖ ≤ ‖((p ^ j : ℕ) : ℤ_[q])‖ := by
    have h1 : ‖((k : ℤ) : ℤ_[q])‖ * ‖toPadicInt q t‖ ≤ ‖((g : ℕ) : ℤ_[q])‖ * ‖toPadicInt q t‖ := by
      rw [← norm_mul, hq, norm_mul, hm, Nat.cast_mul, norm_mul]
      calc ‖((g : ℕ) : ℤ_[q])‖ * ‖((∏ p ∈ g.primeFactors, c p : ℕ) : ℤ_[q])‖ * ‖toPadicInt q z‖
          ≤ ‖((g : ℕ) : ℤ_[q])‖ * ‖((∏ p ∈ g.primeFactors, c p : ℕ) : ℤ_[q])‖ :=
            mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
        _ ≤ ‖((g : ℕ) : ℤ_[q])‖ * ‖toPadicInt q t‖ :=
            mul_le_mul_of_nonneg_left (hprod.trans (hs q).le) (norm_nonneg _)
    exact (le_of_mul_le_mul_right h1 htq).trans hgp
  rw [Nat.cast_pow, norm_pow, PadicInt.norm_p] at hk
  have hk' : ‖((k : ℤ) : ℤ_[q])‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hk
  rw [PadicInt.norm_int_le_pow_iff_dvd] at hk'
  exact Int.natCast_dvd.1 (by exact_mod_cast hk')

end FiniteLevel

section Lift

variable (P : Ideal (𝓞 ℚ̄))

def decompositionDegreeImageIn (L : IntermediateField ℚ ℚ̄) : AddSubgroup ℤ̂ where
  carrier := (fun σ ↦ Multiplicative.toAdd (degree σ)) ''
    ((MulAction.stabilizer Gal(ℚ̄/ℚ) P ⊓ L.fixingSubgroup : Subgroup Gal(ℚ̄/ℚ)) : Set Gal(ℚ̄/ℚ))
  add_mem' := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, by simp⟩
  zero_mem' := ⟨1, one_mem _, by simp⟩
  neg_mem' := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, inv_mem hσ, by simp⟩

theorem isClosed_decompositionDegreeImageIn (L : IntermediateField ℚ ℚ̄) :
    IsClosed (decompositionDegreeImageIn P L : Set ℤ̂) :=
  (((isClosed_stabilizer P).inter (InfiniteGalois.fixingSubgroup_isClosed L)).isCompact.image
    (continuous_toAdd.comp continuous_degree)).isClosed

theorem exists_mem_decompositionDegreeImageIn_ne_zero [P.IsPrime] (p : ℕ) [Fact p.Prime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (L : GroundTheory.Global.FiniteSubfield) (q : Nat.Primes) : ∃ e ∈ decompositionDegreeImageIn P L.1, toPadicInt q e ≠ 0 := by
  obtain ⟨σ, hσP, hσq⟩ := exists_mem_stabilizer_degreeComponent_ne_one (p := p) P q
  set N := (FiniteSubfield.galoisClosure L).1.fixingSubgroup
  have : N.Normal := CyclotomicSymbol.fixingSubgroup_normal (FiniteSubfield.galoisClosure L)
  have hn : N.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨_, ⟨σ ^ N.index, ⟨pow_mem hσP _, IntermediateField.fixingSubgroup_le
    (show L.1 ≤ (FiniteSubfield.galoisClosure L).1 from FiniteSubfield.le_galoisClosure L)
    (N.pow_index_mem σ)⟩, rfl⟩, ?_⟩
  show toPadicInt q (Multiplicative.toAdd (degree (σ ^ N.index))) ≠ 0
  rw [map_pow, toAdd_pow, map_nsmul, toPadicInt_degree, nsmul_eq_mul]
  refine mul_ne_zero (Nat.cast_ne_zero (R := ℤ_[q]).2 hn) fun h ↦ hσq ?_
  rw [← ofAdd_toAdd (degreeComponent q σ), h, ofAdd_zero]

theorem exists_mem_stabilizer_toPadicInt_ne_zero [P.IsPrime] (p : ℕ) [Fact p.Prime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (L : GroundTheory.Global.FiniteSubfield) (σ₀ : Gal(ℚ̄/ℚ)) :
    ∃ h ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, h ∈ L.1.fixingSubgroup ∧
      ∀ q : Nat.Primes, toPadicInt q (Multiplicative.toAdd (degree (σ₀ * h))) ≠ 0 := by
  classical
  choose e he he0 using exists_mem_decompositionDegreeImageIn_ne_zero P p L
  set t₀ := Multiplicative.toAdd (degree σ₀)
  let f : ∀ q : Nat.Primes, ℤ_[q] := fun q ↦ if toPadicInt q t₀ = 0 then toPadicInt q (e q) else 0
  have hf : ∀ q : Nat.Primes, toPadicInt q (ofPadics f) = f q := fun q ↦
    congrFun (toPadics_ofPadics f) q
  have hy : ofPadics f ∈ decompositionDegreeImageIn P L.1 := by
    refine mem_of_forall_toPadicInt _ (isClosed_decompositionDegreeImageIn P L.1) fun q ↦ ?_
    rw [hf]
    by_cases h0 : toPadicInt q t₀ = 0
    · exact ⟨e q, he q, by simp only [f, if_pos h0]⟩
    · exact ⟨0, zero_mem _, by simp only [f, if_neg h0, map_zero]⟩
  obtain ⟨h, ⟨hP, hL⟩, hh⟩ := hy
  have hh : Multiplicative.toAdd (degree h) = ofPadics f := hh
  refine ⟨h, hP, hL, fun q ↦ ?_⟩
  rw [map_mul, toAdd_mul, map_add]
  change toPadicInt q t₀ + toPadicInt q (Multiplicative.toAdd (degree h)) ≠ 0
  rw [hh, hf]
  by_cases h0 : toPadicInt q t₀ = 0
  · simp only [f, if_pos h0]; rw [h0, zero_add]; exact he0 q
  · simp only [f, if_neg h0, add_zero]; exact h0

end Lift

end

end Cyclotomic

end GroundTheory.Global
