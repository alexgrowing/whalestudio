import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpB

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def jLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (w : ℂ) (g : GR n) : ℂ :=
  ∫ x, ((hLoc (g * A * nbEl x * B) : ℂ) ^ w * F0 p q e (g * A * nbEl x * B)) * ψ x

def czLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) [MeasurableSpace (KR n)] (μ : Measure (KR n))
    (w : ℂ) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ

theorem eigen (hI : Iwa) (hM : Mult) (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] (w : ℂ) (y : GR n) :
    ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * A * nbEl x * B) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * A * nbEl x * B)) * ψ x) ∂μ =
      czLoc p q e A B ψ μ w * ((hLoc y : ℂ) ^ w * F0 p q e y) := by
  obtain ⟨p0, k0, hp, hk0, rfl⟩ := hI n y
  have hM1 := (hM n p q e).1
  have hM2 := (hM n p q e).2
  have hJ : ∀ g : GR n, jLoc p q e A B ψ w (p0 * g) =
      ((hLoc p0 : ℂ) ^ w * F0 p q e p0) * jLoc p q e A B ψ w g := by
    intro g
    unfold jLoc
    rw [← integral_const_mul]
    congr 1
    funext x
    have h1 : p0 * g * A * nbEl x * B = p0 * (g * A * nbEl x * B) := by simp only [mul_assoc]
    rw [h1, (hM2 p0 _ hp).1, (hM2 p0 _ hp).2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (by unfold hLoc; positivity) (by unfold hLoc; positivity)]
    ring
  have hne : F0 p q e k0 ≠ 0 := by
    intro h0
    have h2 := (hM1 k0 k0⁻¹ (inv_mem hk0)).1
    rw [mul_inv_cancel, weight_factor_one, h0, zero_mul] at h2
    exact one_ne_zero h2
  let K0 : KR n := ⟨k0, hk0⟩
  have hK0 : (K0 : GR n) = k0 := rfl
  have hshift : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ =
      F0 p q e k0 * (F0 p q e ((K0 * k : KR n) : GR n))⁻¹ := by
    intro k
    rw [Subgroup.coe_mul, hK0, (hM1 k0 k k.2).1, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  calc _ = ∫ k : KR n, ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ((F0 p q e ((K0 * k : KR n) : GR n))⁻¹ * jLoc p q e A B ψ w ((K0 * k : KR n) : GR n)) ∂μ := by
        congr 1
        funext k
        show (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (p0 * k0 * (k : GR n)) = _
        rw [show p0 * k0 * (k : GR n) = p0 * ((K0 * k : KR n) : GR n) by
          rw [Subgroup.coe_mul, hK0, mul_assoc], hJ, hshift k]
        ring
    _ = ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self
          (fun k : KR n => (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n)) K0
    _ = _ := by
        rw [(hM1 p0 k0 hk0).1, (hM1 p0 k0 hk0).2]
        unfold czLoc
        ring

theorem cz_zero (p q : ℕ) (e : ℤ) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] (μ : Measure (KR n)) :
    czLoc p q e (mkG a ha) (mkG b hb) ψ μ 0 = (a.det * b.det) ^ e *
      ∫ k : KR n, (∫ x, f0 p q (mR (k : GR n) * a * nU (herm x) * b) * ψ x) * (f0 p q (mR (k : GR n)))⁻¹ ∂μ := by
  have hmul : ∀ g h : GR n, mR (g * h) = mR g * mR h := fun _ _ => rfl
  have hdetN : ∀ x, (nU (herm x) : M2 n).det = 1 := by
    intro x
    simp [nU, det_fromBlocks_zero₂₁]
  unfold czLoc
  rw [← integral_const_mul]
  congr 1
  funext k
  have hk : (mR (k : GR n)).det ^ e ≠ 0 := by
    apply zpow_ne_zero
    have h1 : (mR (k : GR n)).det * (mR ((k : GR n)⁻¹)).det = 1 := by
      rw [← det_mul, ← hmul, mul_inv_cancel]
      exact det_one
    exact left_ne_zero_of_mul_eq_one h1
  unfold jLoc
  simp only [Complex.cpow_zero, one_mul, F0, hmul, mR_mkG, nbEl, det_mul, hdetN, mul_one, mul_zpow,
    mul_assoc, integral_const_mul]
  generalize (mR (k : GR n)).det ^ e = D at hk ⊢
  have hD := inv_mul_cancel₀ hk
  rw [mul_inv]
  linear_combination (det a ^ e * (det b ^ e *
    ((∫ (x : Fin n → Fin n → ℝ), f0 (↑p) (↑q) (mR (k : GR n) * (a * (nU (herm x) * b))) * ψ x) *
      (f0 (↑p) (↑q) (mR (k : GR n)))⁻¹))) * hD

end PositivityTheory.Rg.Sw.AbsSt
