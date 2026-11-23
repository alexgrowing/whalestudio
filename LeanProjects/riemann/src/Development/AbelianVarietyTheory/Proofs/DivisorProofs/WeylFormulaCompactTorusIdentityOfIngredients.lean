import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeSplitsCompactNoncompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumShiftHolds

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.HCChar (dsChar)

namespace GlobalTheory.PsCo.PcEF

namespace WeylCompactTorusIdentity

theorem alg {W S C M s p x : ℂ} (hs : s * s = 1) (hp : p * p = 1) (hW : W ≠ 0) (hM : M ≠ 0) (hs0 : s ≠ 0)
    (hx : W * x = S * C) : s * x = p * S / (W * (s * M)) * (p * M * C) := by
  have hden : W * (s * M) ≠ 0 := mul_ne_zero hW (mul_ne_zero hs0 hM)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (M * s * s) * hx + (M * S * C) * hs - (M * S * C) * hp

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem prod_tor_pow_eq_wtVal_mul {n : ℕ} (lam : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) (θ : Fin n → ℝ) (w : Equiv.Perm (Fin n)) :
    ∏ a, tor θ a ^ m (w.symm a) =
      GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ * GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ := by
  show ∏ a, Complex.exp (↑(θ a) * Complex.I) ^ m (w.symm a) = _
  unfold GlobalTheory.HCChar.wtVal
  rw [← Complex.exp_add]
  rw [Finset.prod_congr rfl (fun a _ => (Complex.exp_int_mul (↑(θ a) * Complex.I) (m (w.symm a))).symm),
    ← Complex.exp_sum]
  congr 1
  push_cast
  rw [← add_mul, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h2 : ((m (w.symm a) : ℤ) : ℂ) = ((lam (w.symm a) : ℝ) : ℂ) + ((n : ℂ) - 1) / 2 := by
    have h3 := congrArg (fun r : ℝ => (r : ℂ)) (hm (w.symm a))
    push_cast at h3
    exact h3.symm
  simp only [h2, Function.comp_apply]
  ring

end WeylCompactTorusIdentity

open WeylCompactTorusIdentity in

theorem weylFormulaCompactTorusIdentity_of_ingredients : VdmSplit → PhysTor → NumShift → TorusId := by
  intro hV hP hN n ε lam Λ m hm hΛ θ hinj x hx
  have ht0 : ∀ a, tor θ a ≠ 0 := fun a => Complex.exp_ne_zero _
  obtain ⟨hPD, -⟩ := hP n ε θ
  have hVd := hV n ε (tor θ)
  have hWd : GlobalTheory.HCChar.weylDenom θ * GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ =
      ∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b) := GlobalTheory.HCChar.weylDenom_mul θ
  have hNum : (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
      ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, tor θ a ^ m (w.symm a)) =
      (∑ w ∈ GlobalTheory.HCChar.compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ) *
        GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [prod_tor_pow_eq_wtVal_mul lam m hm θ w]
    ring
  have hx' : ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x =
      ((∑ w ∈ GlobalTheory.HCChar.compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ) *
        GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) := by
    rw [hx, ← hNum]
    exact (congrArg (fun μ => ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε μ (tor θ)) (funext hΛ)).trans
      (hN n ε m (fun b : Bool => if b then (0 : ℤ) else (pOf ε : ℤ)) (tor θ) ht0)
  have hV0 : (∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
    exact sub_ne_zero.mpr (fun h => (Finset.mem_Ioi.mp hb).ne (hinj h))
  rw [hVd] at hV0
  have hW0 := left_ne_zero_of_mul hV0
  have hPm0 := right_ne_zero_of_mul (right_ne_zero_of_mul hV0)
  have hh : GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ ≠ 0 := Complex.exp_ne_zero _
  have key := alg (s := (-1) ^ sDeg ε) (p := (-1) ^ (pOf ε * qOf ε)) (neg_one_pow_mul_self _)
    (neg_one_pow_mul_self _) hW0 hPm0 (pow_ne_zero _ (by norm_num)) hx'
  rw [key, hPD, ← hVd, ← hWd]
  unfold GlobalTheory.HCChar.dsChar
  congr 1
  rw [← mul_assoc, mul_div_mul_right _ _ hh]
  try rfl

end GlobalTheory.PsCo.PcEF

end
end

namespace GlobalTheory.PsCo.PcEF
open GlobalTheory.PsCo.PcEG

theorem torusId_full : TorusId := weylFormulaCompactTorusIdentity_of_ingredients vandermonde_splits_compactNoncompact adjointDet_onCompactTorus numShift_holds

end GlobalTheory.PsCo.PcEF
