import Mathlib
import Lemmata.GeneralBFactRightVersion.Imports

noncomputable section

namespace Formalism.MainNotions.N.KillingConditions

def WildProP (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Prop :=
  ∀ (A : ValuationSubring Ω) (p : ℕ), p.Prime → A.valuation ((p : ℕ) : Ω) < 1 →
    ∀ σ : Ω ≃ₐ[E] Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) →
    ∀ N : Subgroup (Ω ≃ₐ[E] Ω), IsOpen (N : Set (Ω ≃ₐ[E] Ω)) → ∃ k : ℕ, σ ^ (p ^ k) ∈ N

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions.WildPf

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)

def IsWild (σ : Ω ≃ₐ[E] Ω) : Prop := ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1

variable {A}

theorem IsWild.one : IsWild A (1 : Ω ≃ₐ[E] Ω) := by
  intro y hy
  have : (1 : Ω ≃ₐ[E] Ω) y / y - 1 = 0 := by
    rw [AlgEquiv.one_apply, div_self hy, sub_self]
  rw [this, map_zero]
  exact zero_lt_one

theorem IsWild.val_div {σ : Ω ≃ₐ[E] Ω} (h : IsWild A σ) {y : Ω} (hy : y ≠ 0) : A.valuation (σ y / y) = 1 := by
  have := Valuation.map_one_add_of_lt (v := A.valuation) (h y hy)
  rwa [add_sub_cancel] at this

theorem IsWild.mul {σ τ : Ω ≃ₐ[E] Ω} (hσ : IsWild A σ) (hτ : IsWild A τ) : IsWild A (σ * τ) := by
  intro y hy
  have hτy : τ y ≠ 0 := (map_ne_zero τ).2 hy
  have e : (σ * τ) y / y - 1 = (σ (τ y) / τ y - 1) * (τ y / y) + (τ y / y - 1) := by
    rw [AlgEquiv.mul_apply]
    field_simp
    ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ (hτ y hy)
  rw [map_mul, hτ.val_div hy, mul_one]
  exact hσ _ hτy

theorem IsWild.pow {σ : Ω ≃ₐ[E] Ω} (h : IsWild A σ) (n : ℕ) : IsWild A (σ ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IsWild.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem val_intCast_le (a : ℤ) : A.valuation ((a : ℤ) : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (intCast_mem A a)

theorem val_natCast_eq_one {p m : ℕ} (hpA : A.valuation ((p : ℕ) : Ω) < 1) (hm : Nat.Coprime m p) :
    A.valuation ((m : ℕ) : Ω) = 1 := by
  have hle : A.valuation ((m : ℕ) : Ω) ≤ 1 := by
    exact (A.valuation_le_one_iff _).2 (natCast_mem A m)
  by_contra hne
  have hlt : A.valuation ((m : ℕ) : Ω) < 1 := lt_of_le_of_ne hle hne
  have hb : ((m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab m p
    rw [hm.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hb' : ((m : ℕ) : Ω) * ((Nat.gcdA m p : ℤ) : Ω) + ((p : ℕ) : Ω) * ((Nat.gcdB m p : ℤ) : Ω) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hb
  have h1 : A.valuation (1 : Ω) < 1 := by
    rw [← hb']
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le _)) hlt
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le _)) hpA
  rw [map_one] at h1
  exact lt_irrefl _ h1

theorem pow_fix {τ : Ω ≃ₐ[E] Ω} {y : Ω} (h : τ y = y) (j : ℕ) : (τ ^ j) y = y := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

theorem fix_of_coprime {p m : ℕ} (hpA : A.valuation ((p : ℕ) : Ω) < 1) (hm : Nat.Coprime m p) {τ : Ω ≃ₐ[E] Ω}
    (hτ : IsWild A τ) (y : Ω) (hy : (τ ^ m) y = y) : τ y = y := by
  have hvm := val_natCast_eq_one (A := A) hpA hm
  have hm0 : ((m : ℕ) : Ω) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvm
    exact zero_ne_one hvm
  set T : Ω := ∑ i ∈ Finset.range m, (τ ^ i) y with hT
  have hτT : τ T = T := by
    have h1 : τ T = ∑ i ∈ Finset.range m, (τ ^ (i + 1)) y := by
      rw [hT, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun i => (τ ^ i) y) m
    have h3 := Finset.sum_range_succ (fun i => (τ ^ i) y) m
    rw [h3, hy] at h2
    have h4 : (τ ^ 0) y = y := rfl
    rw [h4] at h2
    rw [h1]
    exact (add_right_cancel h2).symm
  set z : Ω := (m : Ω) * y - T with hz
  have hzi : ∀ i : ℕ, (τ ^ i) z = (m : Ω) * (τ ^ i) y - T := by
    intro i
    rw [hz, map_sub, map_mul, map_natCast, pow_fix hτT i]
  have hsum : ∑ i ∈ Finset.range m, (τ ^ i) z = 0 := by
    simp only [hzi]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
  have hz0 : z = 0 := by
    by_contra hne
    have h1 : ∑ i ∈ Finset.range m, ((τ ^ i) z / z - 1) = -(m : Ω) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum, zero_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, zero_sub]
    have h2 : A.valuation (∑ i ∈ Finset.range m, ((τ ^ i) z / z - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun i _ => (hτ.pow i) z hne
    rw [h1, Valuation.map_neg, hvm] at h2
    exact lt_irrefl _ h2
  have h5 : (m : Ω) * y = T := sub_eq_zero.1 hz0
  have h6 : (m : Ω) * τ y = (m : Ω) * y := by
    rw [h5, ← hτT, ← h5, map_mul, map_natCast]
  exact mul_left_cancel₀ hm0 h6

theorem exists_pow_fix (σ : Ω ≃ₐ[E] Ω) (y : Ω) (hy : IsIntegral E y) : ∃ n : ℕ, n ≠ 0 ∧ (σ ^ n) y = y := by
  first | exact Bl.general_b_fact_right_version.goal1 .. | (apply Bl.general_b_fact_right_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_version.goal1 <;> assumption)

theorem exists_ppow_fix {p : ℕ} (hp : p.Prime) (hpA : A.valuation ((p : ℕ) : Ω) < 1) {σ : Ω ≃ₐ[E] Ω} (hσ : IsWild A σ)
    (y : Ω) (hy : IsIntegral E y) : ∃ a : ℕ, ∀ k, a ≤ k → (σ ^ (p ^ k)) y = y := by
  obtain ⟨n, hn, hfix⟩ := exists_pow_fix σ y hy
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
  have h1 : (σ ^ (p ^ a)) y = y := by
    refine fix_of_coprime hpA hcop (hσ.pow _) y ?_
    rw [← pow_mul]
    exact hfix
  refine ⟨a, fun k hk => ?_⟩
  have h2 : σ ^ (p ^ k) = (σ ^ (p ^ a)) ^ (p ^ (k - a)) := by
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  rw [h2]
  exact pow_fix h1 _

theorem wildProP (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Formalism.MainNotions.N.KillingConditions.WildProP E Ω := by
  intro A p hp hpA σ hσ N hN
  have hnh : (N : Set (Ω ≃ₐ[E] Ω)) ∈ nhds (1 : Ω ≃ₐ[E] Ω) := hN.mem_nhds N.one_mem
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff E Ω _).1 hnh
  obtain ⟨S, hS⟩ := (Module.finite_def.1 hL : (⊤ : Submodule E L).FG)
  have hint : ∀ s : L, IsIntegral E (s : Ω) := fun s =>
    (isIntegral_algebraMap_iff (algebraMap L Ω).injective).2 (Algebra.IsIntegral.isIntegral s)
  choose a ha using fun s : L => exists_ppow_fix hp hpA (σ := σ) hσ (s : Ω) (hint s)
  refine ⟨S.sup a, hLN ?_⟩
  show σ ^ (p ^ S.sup a) ∈ L.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span E (S : Set L) := by rw [hS]; trivial
  have key : ∀ u : L, u ∈ Submodule.span E (S : Set L) → (σ ^ (p ^ S.sup a)) (u : Ω) = (u : Ω) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem s hs => exact ha s _ (Finset.le_sup hs)
    | zero => simp
    | add u v _ _ hu hv =>
      rw [IntermediateField.coe_add, map_add, hu, hv]
    | smul c u _ hu =>
      rw [IntermediateField.coe_smul, map_smul, hu]
  exact key ⟨x, hx⟩ hx'

end Formalism.MainNotions.N.KillingConditions.WildPf

end
