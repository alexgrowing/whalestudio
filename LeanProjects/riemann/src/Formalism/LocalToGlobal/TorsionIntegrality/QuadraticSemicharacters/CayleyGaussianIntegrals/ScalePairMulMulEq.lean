import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

open Formalism.L2.Th1.F (scalePair)

theorem mul_mem_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    c * z ∈ (scalePair L c hc).lattice ↔ z ∈ L.lattice := by
  rw [(Formalism.L2.Th1.F.homogeneity L c hc).1, inv_mul_cancel_left₀ hc]

theorem herm_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z w : ℂ) :
    Formalism.L2.Th1.F.herm (scalePair L c hc) (c * z) (c * w) = Formalism.L2.Th1.F.herm L z w := by
  have hA := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.1
  have hn : ((‖c‖ : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (norm_pos_iff.mpr hc).ne')
  simp only [Formalism.L2.Th1.F.herm, hA, map_mul]
  have h1 : c * z * (conj c * conj w) = (‖c‖ : ℂ) ^ 2 * (z * conj w) := by
    rw [← Complex.mul_conj' c]; ring
  rw [h1]
  push_cast
  exact mul_div_mul_left _ _ hn

theorem scalePair_mul_mul_eq (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z w : ℂ) :
    Formalism.L2.Th1.F.altE (scalePair L c hc) (c * z) (c * w) = Formalism.L2.Th1.F.altE L z w := by
  simp only [Formalism.L2.Th1.F.altE, herm_scale]

theorem semiChar_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω : ℂ) :
    Formalism.L2.Th1.F.semiChar (scalePair L c hc) (c * ω) = Formalism.L2.Th1.F.semiChar L ω := by
  have h : c * ω / 2 ∈ (scalePair L c hc).lattice ↔ ω / 2 ∈ L.lattice := by
    rw [mul_div_assoc, mul_mem_scale]
  unfold Formalism.L2.Th1.F.semiChar
  by_cases h2 : ω / 2 ∈ L.lattice
  · rw [if_pos h2, if_pos (h.mpr h2)]
  · rw [if_neg h2, if_neg (fun h3 => h2 (h.mp h3))]

theorem th0Char_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ ω : ℂ) :
    Formalism.L2.Th1.F.thetaZeroCharacter (scalePair L c hc) (c * ω₀) (c * ω) = Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω := by
  simp only [Formalism.L2.Th1.F.thetaZeroCharacter, semiChar_scale, scalePair_mul_mul_eq]

theorem smul_mem_stdLat_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (n : Type*) (x : n → ℂ) :
    c • x ∈ stdLat (scalePair L c hc) n ↔ x ∈ stdLat L n := by
  simp only [mem_stdLat, Pi.smul_apply, smul_eq_mul, mul_mem_scale]

theorem stdH_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (n : Type*) [Fintype n] [DecidableEq n] (z w : n → ℂ) :
    stdH (scalePair L c hc) n (c • z) (c • w) = stdH L n z w := by
  simp only [stdH_apply, Pi.smul_apply, smul_eq_mul, herm_scale]

theorem alphaQ_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (n : Type*) [Fintype n] [DecidableEq n] (r : ℝ)
    (x : n → ℂ) : alphaQ r (stdH (scalePair L c hc) n) (c • x) = alphaQ r (stdH L n) x := by
  simp only [alphaQ, qOf, stdH_scale]

theorem stdChar_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) {n : Type*} [Fintype n] (ω₀ : ℂ) (x : n → ℂ) :
    stdChar (scalePair L c hc) (c * ω₀) (c • x) = stdChar L ω₀ x := by
  simp only [stdChar, Pi.smul_apply, smul_eq_mul, th0Char_scale]

theorem CmStdCharScale_proof : CmStdCharScale := by
  intro a b c d ha hd lam hlam h4 hodd h8 n _ _ x hx
  obtain ⟨y, rfl⟩ : ∃ y : n → ℂ, x = lam • y := ⟨lam⁻¹ • x, by rw [smul_inv_smul₀ hlam]⟩
  unfold cmL at hx ⊢
  rw [smul_mem_stdLat_scale] at hx
  rw [alphaQ_scale, stdChar_scale]
  exact CmStdChar_proof a b c d ha hd h4 hodd h8 n y hx

end Formalism.L2.Th1.H
