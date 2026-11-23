import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
open NumberField Polynomial

namespace GlobalTheory

def unitBallSubring (A : Type) [NormedField A] [IsUltrametricDist A] : Subring A :=
  GlobalTheory.ClosedBallValuationSubring.closedBallSubring A

theorem den_eq_one_of_padicNorm_le_one (c : ℚ)
    (h : ∀ q : ℕ, q.Prime → padicNorm q c ≤ 1) : c.den = 1 := by
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  haveI := Fact.mk hq
  have hc : c ≠ 0 := by
    rintro rfl; simp at hne
  have h1 := h q hq
  rw [padicNorm.eq_zpow_of_nonzero hc] at h1
  have hv : 0 ≤ padicValRat q c := by
    by_contra hlt
    push_neg at hlt
    have hq1 : (1 : ℚ) < q := by exact_mod_cast hq.one_lt
    have : (1 : ℚ) < (q : ℚ) ^ (-padicValRat q c) := one_lt_zpow₀ hq1 (by omega)
    linarith
  have hden : 1 ≤ padicValNat q c.den :=
    one_le_padicValNat_of_dvd c.den_nz hqd
  have hnum : padicValInt q c.num = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdvd
    have hcop := c.reduced
    have : q ∣ Nat.gcd c.num.natAbs c.den :=
      Nat.dvd_gcd (Int.natCast_dvd.mp hdvd) hqd
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  unfold padicValRat at hv
  omega

theorem isIntegral_of_forall_padicAlgCl_norm_le_one :
    ∀ (M : Type) [Field M] [NumberField M] (a : M),
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ a‖ ≤ 1) → IsIntegral ℤ a := by
  intro M _ _ a h
  set f := minpoly ℚ a with hf
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hmon : f.Monic := minpoly.monic hint
  have hcoeff : ∀ q : ℕ, q.Prime → ∀ n, padicNorm q (f.coeff n) ≤ 1 := by
    intro q hq n
    haveI := Fact.mk hq
    let S := unitBallSubring (PadicAlgCl q)
    set g := f.map (algebraMap ℚ (PadicAlgCl q)) with hg
    have hroots : ∀ b ∈ g.roots, b ∈ S := by
      intro b hb
      have hb' : b ∈ f.rootSet (PadicAlgCl q) := by
        rw [Polynomial.mem_rootSet]
        obtain ⟨hne, hr⟩ := (mem_roots'.mp hb)
        refine ⟨fun h0 => hne (by rw [hg, h0, Polynomial.map_zero]), ?_⟩
        rw [← eval_map_algebraMap]; exact hr
      rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly] at hb'
      obtain ⟨τ, rfl⟩ := hb'
      exact h q τ
    have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
    have hgmon : g.Monic := hmon.map _
    have hgc : g.coeff n ∈ S := by
      by_cases hn : n ≤ g.natDegree
      · rw [coeff_eq_esymm_roots_of_card hcard hn, hgmon.leadingCoeff, one_mul]
        refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
        unfold Multiset.esymm
        refine S.multiset_sum_mem _ fun x hx => ?_
        obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
        refine S.multiset_prod_mem _ fun y hy => hroots y ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp hs).1 hy
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact S.zero_mem
    have h1 : ‖algebraMap ℚ (PadicAlgCl q) (f.coeff n)‖ ≤ 1 := by
      rw [← coeff_map]; exact hgc
    have e : algebraMap ℚ (PadicAlgCl q) (f.coeff n) =
        ((f.coeff n : ℚ_[q]) : PadicAlgCl q) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.eq_padicNorm] at h1
    exact_mod_cast h1
  have hlift : f ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨(f.coeff n).num, ?_⟩
    have := den_eq_one_of_padicNorm_le_one _ (fun q hq => hcoeff q hq n)
    simpa using Rat.coe_int_num_of_den_eq_one this
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨g, hgm, ?_⟩
  have h0 : aeval a f = 0 := minpoly.aeval ℚ a
  rw [← hg, ← algebraMap_int_eq, aeval_map_algebraMap] at h0
  exact h0

end GlobalTheory
