import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum

theorem IsMinPol.scaleRoots_eq {K : Type} [Field K] {σ : K →+* ℂ} {β : ℂ} {u : K} {p q : K[X]}
    (hp : IsMinPol σ β p) (hq : IsMinPol σ (σ u * β) q) (hu : u ≠ 0) : q = p.scaleRoots u := by
  let := σ.toAlgebra
  have ep := hp.eq_minpoly
  have eq := hq.eq_minpoly
  have hr0 : (p.scaleRoots u).eval₂ σ (σ u * β) = 0 := scaleRoots_eval₂_eq_zero σ hp.2.2
  have hs0 : (q.scaleRoots u⁻¹).eval₂ σ β = 0 := by
    have := scaleRoots_eval₂_eq_zero σ (s := u⁻¹) hq.2.2
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul] at this
  have d1 : q ∣ p.scaleRoots u := by
    rw [eq]; exact minpoly.dvd K (σ u * β) hr0
  have d2 : p ∣ q.scaleRoots u⁻¹ := by
    rw [ep]; exact minpoly.dvd K β hs0
  have hq0 : q.scaleRoots u⁻¹ ≠ 0 := scaleRoots_ne_zero hq.1.ne_zero _
  have le1 : p.natDegree ≤ q.natDegree := by
    have := natDegree_le_of_dvd d2 hq0
    rwa [natDegree_scaleRoots] at this
  exact (eq_of_monic_of_dvd_of_natDegree_le hq.1 ((monic_scaleRoots_iff u).2 hp.1) d1
    (by rw [natDegree_scaleRoots]; exact le1)).symm

end GlobalTheory.FunObj.SqNum

theorem GlobalTheory.FunObj.SqNum.meanVal_vw_smul : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  intro K _ _ _ σ β u p q hp hq hβ hu w
  obtain ⟨hc, hd⟩ := hp.ne_zero hβ
  rw [hp.scaleRoots_eq hq hu]
  unfold GlobalTheory.FunObj.SqNum.meanVal_vw
  rw [natDegree_scaleRoots, coeff_scaleRoots, Nat.sub_zero]
  have hm : vw w (p.coeff 0 * u ^ p.natDegree) = vw w (p.coeff 0) + p.natDegree * vw w u := by
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hc)
        (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 (pow_ne_zero _ hu)),
      ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
  rw [hm]
  have : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
