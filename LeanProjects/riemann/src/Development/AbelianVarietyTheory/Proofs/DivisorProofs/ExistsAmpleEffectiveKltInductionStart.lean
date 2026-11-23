import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigLineBundleKodairaLemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosKltAddSmulEffectiveDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalMultipleOfGloballyKltStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.PairStep

set_option maxHeartbeats 1000000 in

theorem exists_ample_eff_kltAt_start : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (β : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → 0 < β →
      ∃ (A F : CartierDiv X) (a : ℕ), IsAmpleLB (toLB A) ∧ 0 < a ∧ toPic F = a • cls N₀ hN₀ ∧
        ∃ (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ lam < β ∧
          (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧ ∀ y, KltAt p n (Δ + qWeil D₀ m') y := by
  intro hPr X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨A, hA⟩ := toPic_surjective (cls H hH.isLB)
  have hAamp : IsAmpleLB (toLB A) := by
    rw [toPic_apply] at hA
    exact hH.of_lbIso (isLB_toLB A) ((cls_eq_iff (isLB_toLB A) hH.isLB).1 hA)
  obtain ⟨a, E₀, ha, hE₀, hKod⟩ := GlobalTheory.KodairaLemma.exists_nsmul_cls_eq_add_toPic_of_isBig ℂ X p hp N₀ (toLB A) hbig hAamp
  obtain ⟨F, hF⟩ := toPic_surjective (a • cls N₀ hN₀)
  obtain ⟨m, G, hm, hG⟩ := GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt X p n hp hn Δ hΔ hklt
  have hB : IsQCart (qWeil E₀ 1) := ⟨1, E₀, one_pos, hE₀, rfl⟩
  obtain ⟨c₀, hc₀, hc₀k⟩ := GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hn Δ m G (qWeil E₀ 1) hm hG hklt hB
  set q : ℕ := ⌈1 / c₀ + (a : ℚ) * r / β⌉₊ + 1 with hq
  have hqpos : (0 : ℚ) < q := by positivity
  have hqgt : 1 / c₀ + (a : ℚ) * r / β < q := by
    have := Nat.le_ceil (1 / c₀ + (a : ℚ) * r / β)
    rw [hq]; push_cast; linarith
  have hara : (0 : ℚ) ≤ (a : ℚ) * r / β := by positivity
  have hinv : (0 : ℚ) < 1 / c₀ := by positivity
  have h1 : 1 / (q : ℚ) ≤ c₀ := by
    rw [div_le_iff₀ hqpos]
    have : 1 / c₀ < q := by linarith
    rw [div_lt_iff₀ hc₀] at this
    linarith
  have h2 : (a : ℚ) * r / q < β := by
    have : (a : ℚ) * r / β < q := by linarith
    rw [div_lt_iff₀ hβ] at this
    rw [div_lt_iff₀ hqpos]
    linarith
  refine ⟨A, F, a, hAamp, ha, hF, (a : ℚ) * r / q, 1 / q, q, E₀, by omega, hE₀, by positivity, h2, ?_, ?_⟩
  · intro C hC
    have e1 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) (toLB A) (toLB E₀)
      (isLB_lbPow hN₀ a) (isLB_toLB A) (isLB_toLB E₀) 1 1 C hC (by
        rw [cls_lbPow hN₀ a, one_smul, one_smul, ← toPic_apply]
        exact hKod)
    have e2 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) N₀ N₀
      (isLB_lbPow hN₀ a) hN₀ hN₀ a 0 C hC (by rw [cls_lbPow hN₀ a, zero_smul, add_zero])
    have e3 : (interNumRed ℂ C ![toLB E₀] : ℚ) = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
      have : interNumRed ℂ C ![toLB E₀] = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
        rw [e2] at e1; push_cast at e1; linarith
      exact_mod_cast this
    rw [e3]
    have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  · intro y
    have k := (kltAt_lcAt_of_le_coeff X p n hp hn Δ (qWeil E₀ 1) (1 / q) c₀ y hB h1).1 (hc₀k y)
    convert k using 2
    funext z
    simp only [qWeil, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, div_one]
    ring

end GlobalTheory.PairStep
