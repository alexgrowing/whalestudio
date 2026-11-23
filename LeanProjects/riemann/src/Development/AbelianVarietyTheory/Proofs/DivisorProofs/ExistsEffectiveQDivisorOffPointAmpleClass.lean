import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleAddNefIsAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

namespace GlobalTheory

theorem exists_common_den_nonneg (q₁ q₂ : ℚ) (h₁ : 0 ≤ q₁) (h₂ : 0 ≤ q₂) :
    ∃ a b M : ℕ, 0 < M ∧ q₁ = a / M ∧ q₂ = b / M := by
  refine ⟨q₁.num.toNat * q₂.den, q₂.num.toNat * q₁.den, q₁.den * q₂.den,
    Nat.mul_pos q₁.den_pos q₂.den_pos, ?_, ?_⟩
  · have e : ((q₁.num.toNat : ℕ) : ℚ) = q₁.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₁)
    have hd : (q₂.den : ℚ) ≠ 0 := by exact_mod_cast q₂.den_ne_zero
    push_cast
    rw [e, mul_div_mul_right _ _ hd, Rat.num_div_den]
  · have e : ((q₂.num.toNat : ℕ) : ℚ) = q₂.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₂)
    have hd : (q₁.den : ℚ) ≠ 0 := by exact_mod_cast q₁.den_ne_zero
    push_cast
    rw [e, mul_comm (q₁.den : ℚ) (q₂.den : ℚ), mul_div_mul_right _ _ hd, Rat.num_div_den]

theorem exists_eff_off_pt_ample_class : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N₀ : LB X) (A : CartierDiv X) (x : X) (r : ℕ) (lam μ : ℚ), N₀.IsLB → IsNef ℂ N₀ → IsAmpleLB (toLB A) → 0 < r → lam ≤ 1 → 0 < μ → ∃ (M : ℕ) (E : CartierDiv X), 0 < M ∧ E.Eff ∧ x ∉ E.supp ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB E] : ℚ) / M = (1 - lam) * interNumRed ℂ C ![N₀] / r + μ * interNumRed ℂ C ![toLB A] := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro N₀ A x r lam μ hN₀ hNef hA hr hlam hμ
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  obtain ⟨a, b, M, hM, ha, hb⟩ :=
    exists_common_den_nonneg ((1 - lam) / r) μ (div_nonneg (by linarith) hr'.le) hμ.le
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb; simp at hb; linarith
    · exact h
  have hAb : IsAmpleLB (lbPow (toLB A) b) := (isAmpleLB_pow_iff hA.isLB hb1).2 hA
  have hNa : IsNef ℂ (lbPow N₀ a) := hNef.pow hA a
  have hP : (tens (lbPow (toLB A) b) (lbPow N₀ a)).IsLB := isLB_tens hAb.isLB hNa.isLB
  have hPa : IsAmpleLB (tens (lbPow (toLB A) b) (lbPow N₀ a)) :=
    isAmpleLB_of_cls_eq_ample_add_nef ℂ X p hp _ _ _ hAb hNa hP
      (cls_tens hAb.isLB hNa.isLB hP)
  obtain ⟨n, hn, s, hx, -, -⟩ := hPa.exists_affine_le (x := x) (U := ⊤) trivial
  have hgen : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  have hLn := isLB_lbPow hPa.isLB n
  refine ⟨M * n, divOfSec hLn s hgen, Nat.mul_pos hM hn, eff_divOfSec_of_sec hLn s hgen,
    notMem_supp_divOfSec.2 hx, fun C hC => ?_⟩
  have hcls : toPic (divOfSec hLn s hgen) = cls _ hLn :=
    (presents_divOfRatSec hLn (isRatSec_ratOfSec s hgen)).toPic_eq
  have e : cls (toLB (divOfSec hLn s hgen)) (isLB_toLB _) =
      (n * a) • cls N₀ hN₀ + (n * b) • cls (toLB A) (isLB_toLB A) := by
    change toPic (divOfSec hLn s hgen) = _
    rw [hcls, cls_lbPow hPa.isLB, cls_tens hAb.isLB hNa.isLB, cls_lbPow (isLB_toLB A),
      cls_lbPow hN₀]
    rw [smul_add, smul_smul, smul_smul, add_comm]
  rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ N₀ (toLB A) (isLB_toLB _) hN₀ (isLB_toLB A)
    (n * a) (n * b) C hC e]
  have hMn : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  rw [hb, mul_div_right_comm, ha]
  push_cast
  field_simp

end GlobalTheory
