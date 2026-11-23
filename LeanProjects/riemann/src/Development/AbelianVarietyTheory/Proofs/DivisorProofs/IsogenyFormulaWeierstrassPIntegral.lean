import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplierStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IsogFormula

theorem main : ∀ (L : PeriodPair) (α β Ω P : ℂ) (M n : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → MulStable L α → Complex.normSq α = n → 0 < n → 0 < M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))) := by
  intro L α β Ω P M n hβ hβim hΩ hα hnorm hn hM hP hMP
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero] at hnorm
    have h0 : n = 0 := by exact_mod_cast hnorm.symm
    omega
  obtain ⟨S, hS⟩ := kernel_reps_exist L α hα0 hα
  have hcard := kernel_reps_card L α S hα0 hα hS
  have hs2 := quasiPeriodConstIsogeny_thm L α S hα0 hα hS
  obtain ⟨t, m, ht, hm, -⟩ := mul_stable_integral L α hα
  have hcardn : S.card + 1 = n := by
    rw [hnorm] at hcard
    exact_mod_cast hcard
  have hVL := (GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω (M * n) hβ hβim hΩ (Nat.mul_pos hM hn)).2
  have hnat : ∀ (k : ℕ) (x : ℂ), x ∈ L.lattice → (k : ℂ) * x ∈ L.lattice := by
    intro k x hx
    have := L.lattice.nsmul_mem hx k
    simpa [nsmul_eq_mul] using this
  have hconj : ∀ ω ∈ L.lattice, conj α * ω ∈ L.lattice := by
    intro ω hω
    have hc : conj α = (t : ℂ) - α := by rw [← ht]; ring
    rw [hc, sub_mul]
    refine L.lattice.sub_mem ?_ (hα ω hω)
    have := L.lattice.smul_mem t hω
    simpa [zsmul_eq_mul] using this
  have hnT : ∀ T ∈ S, (n : ℂ) * T ∈ L.lattice := by
    intro T hT
    have h1 := hconj _ (hS.1 T hT).1
    have hn' : (n : ℂ) = conj α * α := by
      rw [mul_comm, Complex.mul_conj, hnorm]
      simp
    rw [hn', mul_assoc]
    exact h1
  have hs2' : (α ^ 2 - (n : ℂ)) * s2 L = ∑ T ∈ S, L.weierstrassP T := by
    rw [← hs2, hnorm]
    simp
  have hnc : (n : ℂ) = (S.card : ℂ) + 1 := by exact_mod_cast hcardn.symm
  have key : ((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2)
      - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))
      = ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2 := by
    have e1 : ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2
        = ((M * n : ℕ) : ℂ) ^ 2 * (∑ T ∈ S, L.weierstrassP T - (S.card : ℂ) * L.weierstrassP P) / Ω ^ 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [e1, ← hs2']
    rw [show (α ^ 2 - (n : ℂ)) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)
        = ((α ^ 2 - (n : ℂ)) * s2 L + (1 - (n : ℂ)) * L.weierstrassP P) / Ω ^ 2 by ring]
    rw [hnc]
    ring
  rw [key]
  refine IsIntegral.sum _ (fun T hT => ?_)
  refine hVL T P (hS.1 T hT).2 hP ?_ ?_
  · have h := hnat M _ (hnT T hT)
    rw [show ((M * n : ℕ) : ℂ) * T = (M : ℂ) * ((n : ℂ) * T) by push_cast; ring]
    exact h
  · have h := hnat n _ hMP
    rw [show ((M * n : ℕ) : ℂ) * P = (n : ℂ) * ((M : ℂ) * P) by push_cast; ring]
    exact h

end GlobalTheory.IsogFormula
