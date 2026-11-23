import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AfUnit

variable {p : ℕ} [Fact p.Prime]

theorem exists_nat_mem (v : AwayP p) : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
  have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
  obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
  have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
  refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
  · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
  · rcases Int.natAbs_eq x with h1 | h1
    · rw [← h1]; exact hx
    · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx

theorem val_natCast (v : AwayP p) (m : ℕ) :
    Valued.v ((m : ℕ) : v.1.adicCompletion ℚ) = v.1.valuation ℚ (algebraMap ℤ ℚ (m : ℤ)) := by
  have e : ((m : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (m : ℤ) := by simp
  rw [e, IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _

theorem val_eval_eq_one (c : AfP p) (u : ℕ → ℕ)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β)
    (v : AwayP p) : Valued.v (AfP.eval v c) = 1 := by
  obtain ⟨l, hl0, hlp, hlv⟩ := exists_nat_mem v
  obtain ⟨hcop, β, hβ, e⟩ := h l hl0 hlp
  have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
    rw [val_natCast, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hlv
  have hu : Valued.v ((u l : ℕ) : v.1.adicCompletion ℚ) = 1 := by
    rw [val_natCast]
    refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.1 fun hlt' => ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at hlt'
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ a hlt') (Ideal.mul_mem_left _ b hlv)))
  have hsmall : Valued.v (AfP.eval v (l • β)) < 1 := by
    rw [map_nsmul, nsmul_eq_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hβ v)) hlt
  rw [e, map_add, map_natCast]
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hu]; exact hsmall), hu]

theorem exists_mul_eq_one : ∀ (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ),
    (∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) →
    ∃ c' : AfP p, c * c' = 1 := by
  intro p _ c u h
  have hv := val_eval_eq_one c u h
  have hint : ∀ v : AwayP p, (AfP.eval v c)⁻¹ ∈ v.1.adicCompletionIntegers ℚ := fun v => by
    show Valued.v (AfP.eval v c)⁻¹ ≤ 1
    rw [map_inv₀, hv v, inv_one]
  let c' : AfP p := ⟨fun v => (AfP.eval v c)⁻¹, Filter.Eventually.of_forall hint⟩
  refine ⟨c', Subtype.ext (funext fun v => ?_)⟩
  have hne : AfP.eval v c ≠ 0 := fun h0 => by simpa [h0] using hv v
  exact mul_inv_cancel₀ hne

end GlobalTheory.AfUnit
