import Formalism.PeriodIntegrals.JetsPhW
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralMv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaG
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialFirst
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaF
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialThird
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialFourth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitBall
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralNatCast
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialFifth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialSixth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntMvPderiv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialSecond

noncomputable section

open Classical

namespace PI.JetsPhW.W

open PI.JetsPhW MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

noncomputable def intSub (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.PadicComplexIntegerSubring.intSub p

theorem mem_intSub {x : ℂ_[p]} : x ∈ intSub p ↔ IsIntP x := Iff.rfl

theorem isPadicIntegral_natCast (n : ℕ) : IsIntP (n : ℂ_[p]) :=
  _root_.UpperTheory.Reformulated.B.IsIntegralNatCast.isPadicIntegral_natCast n

theorem intMv_zero : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) :=
  _root_.UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.intMv_zero

theorem intMv_one : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) :=
  _root_.UpperTheory.Reformulated.B.Gwb3.intMv_one

theorem intMv_add {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F + G) :=
  _root_.UpperTheory.Reformulated.B.IntegralPolynomialFirst.intMv_add hF hG

theorem intMv_neg {F : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) : IntegralMv (-F) :=
  _root_.UpperTheory.Reformulated.B.IntegralPolynomialFourth.intMv_neg hF

theorem intMv_sub {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F - G) := by
  rw [sub_eq_add_neg]; exact intMv_add hF (intMv_neg hG)

theorem intMv_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) :=
  _root_.UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul hF hG

theorem intMv_C {c : ℂ_[p]} (hc : IsIntP c) : IntegralMv (C c : MvPowerSeries σ ℂ_[p]) :=
  _root_.UpperTheory.Reformulated.B.IntegralPolynomialThird.intMv_C hc

theorem intMv_X (i : σ) : IntegralMv (X i : MvPowerSeries σ ℂ_[p]) :=
  _root_.UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.intMv_X i

theorem intMv_pderiv {F : MvPowerSeries σ ℂ_[p]} (i : σ) (hF : IntegralMv F) :
    IntegralMv (pderiv ℂ_[p] i F) :=
  _root_.UpperTheory.Reformulated.B.Gwb7.intMv_pderiv i hF

theorem intMv_inv {F : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (h1 : constantCoeff F = 1) :
    ∃ G : MvPowerSeries σ ℂ_[p], IntegralMv G ∧ F * G = 1 :=
  _root_.UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv hF h1

theorem coeff_pow_eq_zero {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {n : ℕ}
    {α : σ →₀ ℕ} (h : Finsupp.degree α < n) : coeff α (f ^ n) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (le_order_pow_of_constantCoeff_eq_zero n hf)

def expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n

theorem coeff_expMv (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := rfl

theorem coeff_expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ Finset.range N, coeff α (f ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [expT, map_sum, map_smul, smul_eq_mul, div_eq_inv_mul]

theorem coeff_expMv_eq_expT {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {α : σ →₀ ℕ}
    {N : ℕ} (hN : Finsupp.degree α < N) : coeff α (expMv f) = coeff α (expT f N) := by
  rw [coeff_expMv, coeff_expT]
  apply Finset.sum_subset
  · intro n hn; simp only [Finset.mem_range] at *; omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [coeff_pow_eq_zero hf (by omega), zero_div]

theorem pderiv_expT (f : MvPowerSeries σ ℂ_[p]) (i : σ) (N : ℕ) :
    pderiv ℂ_[p] i (expT f (N + 1)) = pderiv ℂ_[p] i f * expT f N := by
  simp only [expT, map_sum, Derivation.map_smul, Finset.mul_sum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pderiv_pow, Nat.add_sub_cancel, smul_eq_C_mul, smul_eq_C_mul]
  have hn : ((n + 1 : ℕ) : MvPowerSeries σ ℂ_[p]) = C ((n + 1 : ℕ) : ℂ_[p]) := (map_natCast C _).symm
  have key : ((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p]) = (n.factorial : ℂ_[p])⁻¹ := by
    have h1 : ((n + 1 : ℕ) : ℂ_[p]) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  rw [hn]
  calc C ((n + 1).factorial : ℂ_[p])⁻¹ * (C ((n + 1 : ℕ) : ℂ_[p]) * f ^ n * pderiv ℂ_[p] i f)
      = C (((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p])) * (f ^ n * pderiv ℂ_[p] i f) := by
        rw [map_mul]; ring
    _ = pderiv ℂ_[p] i f * (C (n.factorial : ℂ_[p])⁻¹ * f ^ n) := by rw [key]; ring

theorem pderiv_expMv {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) (i : σ) :
    pderiv ℂ_[p] i (expMv f) = pderiv ℂ_[p] i f * expMv f := by
  ext α
  have h1 : coeff α (pderiv ℂ_[p] i (expMv f)) =
      coeff α (pderiv ℂ_[p] i (expT f (Finsupp.degree α + 1 + 1))) := by
    rw [coeff_pderiv, coeff_pderiv, coeff_expMv_eq_expT hf]
    rw [map_add, Finsupp.degree_single]; omega
  rw [h1, pderiv_expT, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  refine (coeff_expMv_eq_expT hf ?_).symm
  have := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.1 hx)
  rw [map_add] at this; omega

theorem constantCoeff_expMv (f : MvPowerSeries σ ℂ_[p]) : constantCoeff (expMv f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expMv]
  simp

theorem L0 {f c : MvPowerSeries σ ℂ_[p]} (i : σ) (hf : constantCoeff f = 0)
    (hE : IntegralMv (expMv f)) (hc : IntegralMv c) : IntegralMv (c * pderiv ℂ_[p] i f) := by
  obtain ⟨G, hG, hEG⟩ := intMv_inv hE (constantCoeff_expMv f)
  have : c * pderiv ℂ_[p] i f = c * pderiv ℂ_[p] i (expMv f) * G := by
    rw [pderiv_expMv hf, mul_assoc, mul_assoc, hEG, mul_one]
  rw [this]
  exact intMv_mul (intMv_mul hc (intMv_pderiv i hE)) hG

theorem integral_of_simeq_alt {F G c : MvPowerSeries σ ℂ_[p]} (i : σ) (h : Simeq F G) (hc : IntegralMv c) :
    IntegralMv (c * pderiv ℂ_[p] i (F - G)) :=
  L0 i h.1 h.2 hc

end PI.JetsPhW.W
