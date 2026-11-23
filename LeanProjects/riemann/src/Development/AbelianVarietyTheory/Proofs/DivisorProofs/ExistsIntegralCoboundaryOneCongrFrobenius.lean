import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondRoot

theorem charP_mvPowerSeries (σ k : Type) [Field k] (p : ℕ) [CharP k p] :
    CharP (MvPowerSeries σ k) p :=
  charP_of_injective_algebraMap (algebraMap k (MvPowerSeries σ k)).injective p

theorem coeff_pow_char_sum {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) :
    coeff α (f ^ p) = ∑ m ∈ Finset.Iic α, if α = p • m then coeff m f ^ p else 0 := by
  classical
  haveI := charP_mvPowerSeries σ k p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set P : MvPowerSeries σ k := ∑ m ∈ Finset.Iic α, monomial m (coeff m f)
  set g := f - P
  have hg : ∀ m ≤ α, coeff m g = 0 := by
    intro m hm
    simp only [g, P, map_sub, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_Iic.2 hm) h
  have hmul : ∀ h : MvPowerSeries σ k, coeff α (h * g) = 0 := by
    intro h
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
    rw [hg q.2 (hq' ▸ le_add_self), mul_zero]
  have hf : f = P + g := by simp [g]
  have hgp : coeff α (g ^ p) = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp0
    rw [hn, pow_succ]; exact hmul _
  rw [show f ^ p = (P + g) ^ p from congrArg (· ^ p) hf, add_pow_char, map_add, hgp, add_zero]
  simp only [P]
  rw [sum_pow_char, map_sum]
  simp only [monomial_pow, coeff_monomial]

theorem coeff_smul_pow_char {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (β : σ →₀ ℕ) : coeff (p • β) (f ^ p) = coeff β f ^ p := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [coeff_pow_char_sum, Finset.sum_eq_single β]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro hα
    exact hb (smul_right_injective _ hp0 hα).symm
  · intro hn
    exact absurd (Finset.mem_Iic.2 (le_smul_of_one_le_left zero_le (Nat.one_le_iff_ne_zero.2 hp0))) hn

theorem coeff_pow_char_of_not {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) (h : ¬∃ β, p • β = α) : coeff α (f ^ p) = 0 := by
  classical
  rw [coeff_pow_char_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg]
  intro hα; exact h ⟨b, hα.symm⟩

end GlobalTheory.SmallSecondRoot

namespace GlobalTheory.SmallSecondRoot

theorem exists_integral_cob1_congr_of_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv d μ hμ c t ht hct
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hroot : ∀ a : O, ∃ r : O, r ^ p = a := by
    intro a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Nat.pos_of_ne_zero hp0)
    have h1 : v z ≤ 1 := by
      have : v z ^ p ≤ 1 := by rw [← map_pow, hz]; exact hv.map_le_one a
      exact (pow_le_one_iff_of_nonneg zero_le hp0).1 this
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩
  choose rt hrt using hroot
  let u : MvPowerSeries (Fin d) O := fun β => rt (coeff (p • β) t)
  have hu : ∀ β, coeff β u = rt (coeff (p • β) t) := fun β => rfl
  refine ⟨u, fun α => ?_⟩
  let res := IsLocalRing.residue O
  have hres : ∀ x : O, ¬ IsUnit x ↔ res x = 0 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast res, ← hres]; exact Fact.out)
  have hμb : ∀ i, constantCoeff (map res (μ i)) = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ.const i, map_zero]
  have ht' : map res t = (map res u) ^ p := by
    ext γ
    rw [coeff_map]
    by_cases h : ∃ β, p • β = γ
    · obtain ⟨β, rfl⟩ := h
      rw [coeff_smul_pow_char, coeff_map, hu, ← map_pow, hrt]
    · rw [coeff_pow_char_of_not _ _ _ h, ← hres]
      apply ht
      by_contra hall
      push_neg at hall
      refine h ⟨Finsupp.mapRange (· / p) (Nat.zero_div p) γ, ?_⟩
      ext i
      simp [Nat.mul_div_cancel' (hall i)]
  have hcob : map res (cob1 μ t) = (cob1 (fun i => map res (μ i)) (map res u)) ^ p := by
    haveI := charP_mvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField O) p
    rw [SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, ht']
    unfold cob1 inL inR
    rw [subst_pow (hasSubst_of_constantCoeff_zero hμb),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), sub_pow_char,
      sub_pow_char]
  have h1 := (hres _).1 (hct α)
  rw [map_sub, sub_eq_zero, ← coeff_map, hcob, coeff_smul_pow_char, map_pow] at h1
  have h3 : coeff α (cob1 (fun i => map res (μ i)) (map res u)) = res (coeff α c) :=
    frobenius_inj _ p h1
  rw [hres, map_sub, sub_eq_zero, ← h3, ← SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, coeff_map]

end GlobalTheory.SmallSecondRoot
