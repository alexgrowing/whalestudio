import Formalism.LocalToGlobal.CharacterGerms.CanonicalGaugeFirstPartialLawEq
import Formalism.LocalToGlobal.CharacterGerms.CoeffPowCharFrobenius

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace PhPowP

open PartialDerivEval

section Gen

variable {C : Type} [Field C] {V : VF C}

theorem frob_mv {σ : Type} {A B : MvPowerSeries σ C} (hA : IntS V A) (hB : IntS V B) (μ : σ →₀ ℕ) :
    V.MM (coeff μ ((A + B) ^ V.l - A ^ V.l - B ^ V.l)) := by
  have e : (A + B) ^ V.l - A ^ V.l - B ^ V.l = MvPowerSeries.C (V.l : C) *
      ∑ k ∈ Finset.Ioo 0 V.l, A ^ k * B ^ (V.l - k) * MvPowerSeries.C ((V.l.choose k / V.l : ℕ) : C) := by
    rw [add_pow_prime_eq' V.l_prime A B]
    simp only [map_natCast]
    ring
  rw [e, coeff_C_mul, map_sum, mul_comm]
  refine ValuationNonnegativity.mm_mul_int (VF.Ge.sum fun k _ => ?_) FrobP.mm_l
  rw [coeff_mul_C]
  exact VF.Ge.mul_int (intS_mul (intS_pow hA k) (intS_pow hB _) μ) (VF.ge_natCast _)

theorem frob_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C) (hf : ∀ i, IntS V (f i))
    (μ : σ →₀ ℕ) : V.MM (coeff μ ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow V.l_prime.ne_zero, sub_zero, map_zero]
    exact ValuationNonnegativity.mm_zero
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    have hS : IntS V (∑ i ∈ s, f i) := intS_sum _ fun i _ => hf i
    have e : (f b + ∑ i ∈ s, f i) ^ V.l - (f b ^ V.l + ∑ i ∈ s, f i ^ V.l) =
        ((f b + ∑ i ∈ s, f i) ^ V.l - f b ^ V.l - (∑ i ∈ s, f i) ^ V.l) +
          ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by ring
    rw [e, map_add]
    exact ValuationNonnegativity.mm_add (frob_mv (hf b) hS μ) ih

theorem monomial_pow' {σ : Type} (β : σ →₀ ℕ) (a : C) :
    ∀ n : ℕ, (monomial β a) ^ n = monomial (n • β) (a ^ n)
  | 0 => by
    ext μ
    rw [pow_zero, zero_smul, pow_zero, coeff_one, coeff_monomial]
  | n + 1 => by
    rw [pow_succ, monomial_pow' β a n, monomial_mul_monomial, succ_nsmul, pow_succ]

def divL {σ : Type} (l : ℕ) (α : σ →₀ ℕ) : σ →₀ ℕ := Finsupp.mapRange (fun n => n / l) (Nat.zero_div l) α

theorem divL_apply {σ : Type} (l : ℕ) (α : σ →₀ ℕ) (t : σ) : divL l α t = α t / l := by
  simp [divL]

theorem frobPowMv {σ : Type} (F : MvPowerSeries σ C) (hF : IntS V F) (α : σ →₀ ℕ) :
    V.MM (coeff α (F ^ V.l) - if ∀ t, V.l ∣ α t then coeff (divL V.l α) F ^ V.l else 0) := by
  have hl0 : 0 < V.l := V.l_prime.pos
  obtain ⟨P, hPdef⟩ : ∃ P : MvPowerSeries σ C, P = ∑ β ∈ Finset.Iic α, monomial β (coeff β F) := ⟨_, rfl⟩
  have hmon : ∀ β, IntS V (monomial β (coeff β F)) := fun β μ => by
    rw [coeff_monomial]
    split_ifs
    · exact hF β
    · exact VF.Ge.zero 0
  have e1 : coeff α (F ^ V.l) = coeff α (P ^ V.l) := by
    obtain ⟨R, hR⟩ := sub_dvd_pow_sub_pow F P V.l
    have h0 : coeff α (F ^ V.l - P ^ V.l) = 0 := by
      rw [hR, coeff_mul]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx1 : x.1 ≤ α := by
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
        exact le_self_add
      have hc : coeff x.1 (F - P) = 0 := by
        rw [map_sub, sub_eq_zero, hPdef, map_sum]
        simp only [coeff_monomial]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_Iic.2 hx1)]
      rw [hc, zero_mul]
    rwa [map_sub, sub_eq_zero] at h0
  have e2 := frob_sum (Finset.Iic α) (fun β => monomial β (coeff β F)) hmon α
  have e3 : coeff α (∑ β ∈ Finset.Iic α, (monomial β (coeff β F)) ^ V.l) =
      if ∀ t, V.l ∣ α t then coeff (divL V.l α) F ^ V.l else 0 := by
    rw [map_sum]
    simp only [monomial_pow', coeff_monomial]
    split_ifs with hdiv
    · have hβ : α = V.l • divL V.l α := by
        ext t
        rw [Finsupp.smul_apply, smul_eq_mul, divL_apply, Nat.mul_div_cancel' (hdiv t)]
      rw [Finset.sum_eq_single (divL V.l α)]
      · rw [if_pos hβ]
      · intro b _ hb
        rw [if_neg]
        intro h
        apply hb
        ext t
        have := congrArg (fun f : σ →₀ ℕ => f t) (h.symm.trans hβ)
        simp only [Finsupp.smul_apply, smul_eq_mul] at this
        exact Nat.eq_of_mul_eq_mul_left hl0 this
      · intro h
        exfalso
        apply h
        rw [Finset.mem_Iic, Finsupp.le_def]
        intro t
        rw [divL_apply]
        exact Nat.div_le_self _ _
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro h
      apply hdiv
      intro t
      rw [h, Finsupp.smul_apply, smul_eq_mul]
      exact Nat.dvd_mul_right _ _
  rw [e1, ← e3, ← map_sub, hPdef]
  exact e2

end Gen

section Slice

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

end Slice

section FBs

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

end FBs

end PhPowP

end Formalism.L2.FormalSeriesBounds
