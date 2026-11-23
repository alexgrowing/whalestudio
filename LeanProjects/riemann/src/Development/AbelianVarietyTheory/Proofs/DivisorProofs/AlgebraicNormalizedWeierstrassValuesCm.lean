import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplierStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgebraicitySecondEisenstein

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L →
    IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  intro L β Ω hst him hΩ
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => mem_algebraicClosure_iff.symm
  have intAlg : ∀ x : ℂ, IsIntegral ℤ x → x ∈ algebraicClosure ℚ ℂ := fun x hx =>
    (alg x).1 (hx.tower_top (A := ℚ)).isAlgebraic
  have natMem : ∀ k : ℕ, (k : ℂ) ∈ algebraicClosure ℚ ℂ := fun k => natCast_mem _ k
  have part2 : ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
    intro M P hM hP
    obtain ⟨h1, -⟩ := GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω M hst him hΩ hM
    obtain ⟨i1, i2⟩ := h1 P hP
    have a1 := intAlg _ i1
    have a2 := intAlg _ i2
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [mul_div_assoc] at a1 a2
    have c1 : (12 * (M : ℂ) ^ 2) = ((12 * M ^ 2 : ℕ) : ℂ) := by push_cast; ring
    have c2 : ((M : ℂ) ^ 3) = ((M ^ 3 : ℕ) : ℂ) := by push_cast; ring
    have n1 : (12 * (M : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hMc)
    have n2 : ((M : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ hMc
    constructor
    · rw [alg]
      have := div_mem a1 (c1 ▸ natMem (12 * M ^ 2))
      rwa [mul_div_cancel_left₀ _ n1] at this
    · rw [alg]
      have := div_mem a2 (c2 ▸ natMem (M ^ 3))
      rwa [mul_div_cancel_left₀ _ n2] at this
  refine ⟨?_, part2⟩
  have hβ0 : β ≠ 0 := by rintro rfl; simp at him
  obtain ⟨S, hS⟩ := kernel_reps_exist L β hβ0 hst
  have hcard := kernel_reps_card L β S hβ0 hst hS
  obtain ⟨t, n, ht, hn, hq⟩ := mul_stable_integral L β hst
  have hs2 := cm_s2 L β S hst him hS
  have hconj : MulStable L (conj β) := fun ω hω => by
    have e : conj β * ω = t • ω - β * ω := by rw [zsmul_eq_mul, ← ht]; ring
    rw [e]
    exact sub_mem (Submodule.smul_mem _ t hω) (hst ω hω)
  have hM : ((S.card + 1 : ℕ) : ℂ) = conj β * β := by
    rw [← Complex.normSq_eq_conj_mul_self]
    have := congrArg (fun r : ℝ => (r : ℂ)) hcard
    push_cast at this ⊢
    exact this
  have hP : ∀ P ∈ S, L.weierstrassP P / Ω ^ 2 ∈ algebraicClosure ℚ ℂ := fun P hP => by
    have hmem : ((S.card + 1 : ℕ) : ℂ) * P ∈ L.lattice := by
      rw [hM, mul_assoc]; exact hconj _ (hS.1 P hP).1
    exact (alg _).1 (part2 _ P (Nat.succ_pos _) hmem).1
  have hβint : IsIntegral ℤ β := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simpa using hq
  have hβm := intAlg _ hβint
  have hcm : conj β ∈ algebraicClosure ℚ ℂ := by
    have e : conj β = (t : ℂ) - β := by rw [← ht]; ring
    rw [e]; exact sub_mem (intCast_mem _ t) hβm
  rw [alg, hs2, div_div, mul_comm (β * _), ← div_div, Finset.sum_div]
  exact div_mem (sum_mem hP) (mul_mem hβm (sub_mem hβm hcm))

end GlobalTheory.AlgebraicitySecondEisenstein
