import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR

noncomputable section

namespace Formalism.L2.Th1.E

namespace ScaledModelNorms

open Formalism.L2.Th1

theorem dwp_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (F.scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  have h := F.Homog.tsum_scale L c hc (fun w => -2 / (c * z - w) ^ 3)
  rw [← (PeriodPair.hasSum_derivWeierstrassP _ (c * z)).tsum_eq,
    ← (PeriodPair.hasSum_derivWeierstrassP L z).tsum_eq, h, ← tsum_mul_left]
  congr 1
  funext w
  rw [← mul_sub, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

variable (l : ℕ) [Fact l.Prime]

theorem norm_nat {N : ℕ} (h : ¬ l ∣ N) : ‖(N : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  have e : (N : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (N : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    simp
  rw [e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 h

theorem norm_two (hl : 5 ≤ l) : ‖(2 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  simpa using norm_nat l h

theorem norm_four (hl : 5 ≤ l) : ‖(4 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  simpa using norm_nat l h

theorem intCurve_short (hl : 5 ≤ l) (g2 g3 : ℂ_[l]) (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1)
    (hD : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) : IntCurve (A.shortW g2 g3) := by
  have hΔ : (A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
    simp only [A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [A.shortW]
  · simp [A.shortW]
  · simp [A.shortW]
  · show ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, norm_four l hl, div_one]; exact h2
  · show ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, norm_four l hl, div_one]; exact h3
  · rw [hΔ]; exact hD

variable (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem nonsing (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, WeierstrassCurve.Affine.equation_iff]
  have h := congrArg ι (PeriodPair.derivWeierstrassP_sq L t ht)
  simp only [map_sub, map_mul, map_pow, map_ofNat] at h
  show (ι (L.derivWeierstrassP t) / 2) ^ 2 + 0 * ι (L.weierstrassP t) * (ι (L.derivWeierstrassP t) / 2) +
      0 * (ι (L.derivWeierstrassP t) / 2) =
    ι (L.weierstrassP t) ^ 3 + 0 * ι (L.weierstrassP t) ^ 2 + (-ι L.g₂ / 4) * ι (L.weierstrassP t) +
      (-ι L.g₃ / 4)
  linear_combination (1 / 4 : ℂ_[l]) * h

theorem ptOf_notMem (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (nonsing l L ι hΔ t ht) := by
  unfold ptOf
  rw [dif_pos ⟨ht, nonsing l L ι hΔ t ht⟩]

theorem px_ptOf (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    px (curveL l L ι) (ptOf l L ι t) = ι (L.weierstrassP t) := by
  rw [ptOf_notMem l L ι hΔ t ht]
  rfl

theorem py_ptOf (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    py (curveL l L ι) (ptOf l L ι t) = ι (L.derivWeierstrassP t) / 2 := by
  rw [ptOf_notMem l L ι hΔ t ht]
  rfl

end ScaledModelNorms

open Formalism.L2.Th1 in

theorem cm_integrality_of_torsion_points (hP : PtOfInt) : CMIntegrality := by
  intro L l _ hl ι lam hlam h2 h3 hD z N hN hlN hNz hz
  have hμ0 : ι.symm lam ≠ 0 := by simpa using hlam
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hμ0
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L (ι.symm lam)⁻¹ hc
  have hιc : ι (ι.symm lam)⁻¹ = lam⁻¹ := by simp
  have hg2' : ι (F.scalePair L (ι.symm lam)⁻¹ hc).g₂ = lam ^ 4 * ι L.g₂ := by
    rw [hg2, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
  have hg3' : ι (F.scalePair L (ι.symm lam)⁻¹ hc).g₃ = lam ^ 6 * ι L.g₃ := by
    rw [hg3, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
  have hInt : IntCurve (curveL l (F.scalePair L (ι.symm lam)⁻¹ hc) ι) := by
    unfold curveL
    rw [hg2', hg3']
    exact ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD
  have hcz : (ι.symm lam)⁻¹ * z ∉ (F.scalePair L (ι.symm lam)⁻¹ hc).lattice := by
    rw [hmem, inv_mul_cancel_left₀ hc]; exact hz
  have hNcz : (N : ℂ) * ((ι.symm lam)⁻¹ * z) ∈ (F.scalePair L (ι.symm lam)⁻¹ hc).lattice := by
    rw [hmem, mul_left_comm, inv_mul_cancel_left₀ hc]; exact hNz
  obtain ⟨hx, hy⟩ := hP l (F.scalePair L (ι.symm lam)⁻¹ hc) ι hInt _ N hN hlN hNcz hcz
  have hΔ : (curveL l (F.scalePair L (ι.symm lam)⁻¹ hc) ι).Δ ≠ 0 := by
    intro h0
    have := hInt.2.2.2.2.2
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [ScaledModelNorms.px_ptOf l _ ι hΔ _ hcz, hwp, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv] at hx
  rw [ScaledModelNorms.py_ptOf l _ ι hΔ _ hcz, ScaledModelNorms.dwp_scale L _ hc, norm_div, ScaledModelNorms.norm_two l hl, div_one,
    map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv] at hy
  exact ⟨hx, hy⟩

theorem cm_integrality_of_halves : CMTorsionValuesOfIntegralAndUnramified := by
  intro hI hK d L hd hd4 hcm l _ hl hld ι lam hlam hk2 hk3 h2 h3 hD z N hN hlN hNz hz
  obtain ⟨a, b⟩ := hK d L hd hd4 hcm l hl hld ι lam hlam hk2 hk3 h2 h3 hD z N hN hlN hNz hz
  obtain ⟨c, e⟩ := hI L l hl ι lam hlam h2 h3 hD z N hN hlN hNz hz
  exact ⟨a, b, c, e⟩

end Formalism.L2.Th1.E
