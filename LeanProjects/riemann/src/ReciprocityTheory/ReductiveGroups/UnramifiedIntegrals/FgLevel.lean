import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnLat
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgTorInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnTwo
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KapUnit
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem half_cubic (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hM : LatModel l L ι g2 g3) :
    4 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 3 - g2 * ι (L.weierstrassP (L.ω₁ / 2)) - g3 = 0 := by
  have hd : L.derivWeierstrassP (L.ω₁ / 2) = 0 :=
    (F.pDerivZero L _ L.ω₁_div_two_notMem_lattice).2
      (by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact L.ω₁_mem_lattice)
  have h := L.derivWeierstrassP_sq _ L.ω₁_div_two_notMem_lattice
  rw [hd] at h
  have h' := congrArg ι h
  simp only [map_pow, map_mul, map_sub, map_zero, map_ofNat] at h'
  rw [hM.eq2, hM.eq3, ← h']
  norm_num

theorem half_prod_norm (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (S : Finset ℂ) (hS : F.IsKerReps L (l : ℂ) S)
    (hκ : ‖3 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 2 - g2 / 4‖ = 1) :
    ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L.weierstrassP (L.ω₁ / 2)) - ι (L.weierstrassP P)‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have h := congrArg ι (an_two L l (hlp.odd_of_ne_two hl) S hS L.ω₁ L.ω₁_mem_lattice
    L.ω₁_div_two_notMem_lattice)
  simp only [map_pow, map_mul, map_prod, map_sub, map_natCast, map_div₀, map_ofNat] at h
  rw [← hM.eq2] at h
  have hn := congrArg norm h
  rw [norm_pow, norm_pow _ (l ^ 2 - 1), hκ, one_pow, norm_mul, norm_prod] at hn
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 hn

theorem level_le (L : PeriodPair) (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3))‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := by omega
  obtain ⟨L', hM, -⟩ := good_lattice l L ι g2 g3 hg
  obtain ⟨-, -, h2, h3, hΔ, -⟩ := hg
  have h22 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd (l := l) (n := 2)
      (fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h))
    simpa using this
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hst : F.MulStable L' (l : ℂ) := fun ω hω => by
    have := L'.lattice.smul_mem (l : ℤ) hω
    simpa using this
  obtain ⟨S, hS⟩ := F.kerRepsExist L' (l : ℂ) hl0 hst
  have hcard : S.card + 1 = l ^ 2 := by
    have := F.kerRepsCard L' (l : ℂ) S hl0 hst hS
    rw [Complex.normSq_natCast] at this
    have h' : ((S.card + 1 : ℕ) : ℝ) = ((l ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [this]
      ring
    exact_mod_cast h'
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl2 L' ι g2 g3 hM l hlp.pos S hS
  obtain ⟨e', he'0, he'i, he'l⟩ := mulN_integral (curve_law g2 g3 h2 h3 h22) l
  have hee : e' = (uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3) :=
    mult_unique g2 g3 _ e' he'0 he'l
  rw [← hee] at hsq ⊢
  obtain ⟨hAi, hA0, -⟩ :=
    A.bridgeCurve ℂ_[l] (A.shortW g2 g3) (shortW_intModel g2 g3 h2 h3 h22)
  have hAi' : IntegralPS (A.xS (A.shortW g2 g3)) := (integralPS_iff_mv _).2 hAi
  have hGi := integral_of_sq_eq he'i he'0 hUi hU0 hsq
  have hb := gauss_bound S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ hGi
  obtain ⟨he1, hκ⟩ := kap_unit g2 g3 _ h2 h3 hΔ h22 (half_cubic l L' ι g2 g3 hM)
  have hp := half_prod_norm l hl2 L' ι g2 g3 hM S hS hκ
  have hle : ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L'.weierstrassP (L'.ω₁ / 2)) - ι (L'.weierstrassP P)‖
      ≤ ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, max 1 ‖ι (L'.weierstrassP P)‖ := by
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Finset.prod_le_prod (fun P _ => norm_nonneg _) fun P _ => ?_
    exact (norm_sub_le_max_Cl l _ _).trans (max_le_max he1 le_rfl)
  rw [hp] at hle
  obtain ⟨i, hi, hi1⟩ := unit_coeff_mul hUi hGi (by rw [hU0, norm_one]) _
    (gauss_unit S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ (le_antisymm hb hle))
  refine unit_coeff_of_sq he'i (l ^ 2) ⟨i + 2, by omega, ?_⟩
  rw [hsq, mul_assoc, coeff_X_pow_mul]
  exact hi1

end ReciprocityTheory.ChartRestriction.L1
