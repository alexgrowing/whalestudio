import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgIsoU
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgGauss
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgMulN
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem le_one_of_prod_max_le_one {α : Type} (S : Finset α) (f : α → ℝ)
    (h : ∏ P ∈ S, max 1 (f P) ≤ 1) (Q : α) (hQ : Q ∈ S) : f Q ≤ 1 := by
  classical
  rw [← Finset.mul_prod_erase S _ hQ] at h
  have h1 : (1 : ℝ) ≤ ∏ P ∈ S.erase Q, max 1 (f P) :=
    Finset.one_le_prod fun P _ => le_max_left _ _
  have h2 : max 1 (f Q) ≤ max 1 (f Q) * ∏ P ∈ S.erase Q, max 1 (f P) :=
    le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) h1
  exact (le_max_right _ _).trans (h2.trans h)

theorem tor_integral (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n) (P : ℂ)
    (hP : (n : ℂ) * P ∈ L.lattice) (hP' : P ∉ L.lattice) :
    ‖ι (L.weierstrassP P)‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP P)‖ ≤ 1 := by
  have hlp : l.Prime := Fact.out
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd l (n := 2)
      (fun h => hl ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h))
    simpa using this
  have hnn : ‖(n : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd l hln
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hst : F.MulStable L (n : ℂ) := fun ω hω => by
    have := L.lattice.nsmul_mem hω n
    rwa [nsmul_eq_mul] at this
  obtain ⟨S, hS⟩ := F.kerRepsExist L (n : ℂ) hn0 hst
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl L ι g2 g3 hM n hn S hS
  obtain ⟨e, he0, hei, hel⟩ := mulN_integral (curve_law g2 g3 hM.n2 hM.n3 h2) n
  have hee := mult_unique g2 g3 (n : ℂ_[l]) e he0 hel
  rw [← hee] at hsq
  have hG := integral_of_sq_eq hei he0 hUi hU0 hsq
  obtain ⟨hxi, hx0, -, -⟩ := A.bridgeCurve ℂ_[l] (A.shortW g2 g3)
    (shortW_intModel g2 g3 hM.n2 hM.n3 h2)
  have hxi' : IntegralPS (A.xS (A.shortW g2 g3)) := (integralPS_iff_mv _).2 hxi
  have hb := gauss_bound S (fun P => ι (L.weierstrassP P)) _ hxi' hx0 _ hG
  rw [norm_pow, hnn, one_pow, one_mul] at hb
  obtain ⟨Q, hQ, hPQ⟩ := hS.2.2 P hP hP'
  have hxQ : ‖ι (L.weierstrassP Q)‖ ≤ 1 :=
    le_one_of_prod_max_le_one S (fun P => ‖ι (L.weierstrassP P)‖) hb Q hQ
  have hPQ' : L.weierstrassP P = L.weierstrassP Q := by
    have := L.weierstrassP_add_coe Q ⟨P - Q, hPQ⟩
    simpa using this
  have hx : ‖ι (L.weierstrassP P)‖ ≤ 1 := by rw [hPQ']; exact hxQ
  refine ⟨hx, ?_⟩
  have hrel := congrArg ι (L.derivWeierstrassP_sq P hP')
  simp only [map_pow, map_sub, map_mul, ← hM.eq2, ← hM.eq3] at hrel
  have h4 : ‖ι (4 : ℂ)‖ ≤ 1 := by
    have : ι (4 : ℂ) = ((4 : ℕ) : ℂ_[l]) := by
      rw [← map_natCast ι 4]; norm_num
    rw [this]
    exact IsUltrametricDist.norm_natCast_le_one ℂ_[l] 4
  have hy2 : ‖ι (L.derivWeierstrassP P)‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hrel]
    refine (norm_sub_le_max_Cl l _ _).trans (max_le ?_ hM.n3)
    refine (norm_sub_le_max_Cl l _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ h4 (by positivity) (pow_le_one₀ (norm_nonneg _) hx)
    · rw [norm_mul]
      exact mul_le_one₀ hM.n2 (norm_nonneg _) hx
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hy2

end ReciprocityTheory.ChartRestriction.L1
