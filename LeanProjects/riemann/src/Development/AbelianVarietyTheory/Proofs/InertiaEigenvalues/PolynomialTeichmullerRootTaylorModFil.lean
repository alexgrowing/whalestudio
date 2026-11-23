import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltrationStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.ExpImage.PolyTaylor

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {R : Type*} [CommRing R]

theorem eval₂_mem_zero (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 0) (q : Polynomial R) : q.eval₂ φ τ ∈ FilB P 0 := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Submodule.sum_mem _ fun k _ => FilB_zero_mul (hφ _) (by simpa using FilB_pow hτ k)

theorem trunc_mul_sub_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (f g : PowerSeries R) :
    (f.trunc m).eval₂ φ τ * (g.trunc m).eval₂ φ τ - ((f * g).trunc m).eval₂ φ τ ∈
      FilB P (m : ℤ) := by
  have hd : Polynomial.X ^ m ∣ f.trunc m * g.trunc m - (f * g).trunc m := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd,
      PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hd, ← Polynomial.coe_mul,
      Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hd
  rw [← Polynomial.eval₂_mul, ← Polynomial.eval₂_sub, hq, Polynomial.eval₂_mul,
    Polynomial.eval₂_X_pow, mul_comm]
  exact FilB_zero_mul (eval₂_mem_zero φ hφ (FilB_anti zero_le_one hτ) q)
    (by simpa using FilB_pow hτ m)

theorem eval₂_sub_trunc_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (E : PowerSeries R) {v : P.R.BdR} (hv : v ∈ FilB P 0)
    (hE : v - (E.trunc m).eval₂ φ τ ∈ FilB P (m : ℤ)) (p : Polynomial R) :
    p.eval₂ φ v - ((Polynomial.aeval E p).trunc m).eval₂ φ τ ∈ FilB P (m : ℤ) := by
  have hτ0 := FilB_anti zero_le_one hτ
  induction p using Polynomial.induction_on with
  | C a =>
    rcases m with _ | m
    · exact sub_mem (eval₂_mem_zero φ hφ hv _) (eval₂_mem_zero φ hφ hτ0 _)
    · rw [Polynomial.aeval_C, ← PowerSeries.C_eq_algebraMap, PowerSeries.trunc_C]
      simp
  | add p q hp hq =>
    have := add_mem hp hq
    rw [map_add, map_add, Polynomial.eval₂_add, Polynomial.eval₂_add]
    convert this using 1
    ring
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_X]
    have h1 := FilB_zero_mul hv h
    have h2 := FilB_zero_mul (eval₂_mem_zero φ hφ hτ0
      ((Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)).trunc m)) hE
    have h3 := trunc_mul_sub_mem φ hφ hτ m
      (Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)) E
    have := add_mem (add_mem h1 h2) h3
    convert this using 1
    ring

theorem poly_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (s : ℕ) (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ (p : Polynomial ↥LL.1) (m : ℕ), Polynomial.eval₂ (ι : ↥LL.1 →+* P.R.BdR) (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) p - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) p)) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈ GlobalTheory.ExpImage.FilB P (m : ℤ) := by
  intro l _ P AI T LL s ζ ι hζ p m
  have hφ : ∀ x, (ι : ↥LL.1 →+* P.R.BdR) x ∈ FilB P 0 := EmbFil.emb_mem_fil_zero l P AI T LL ι
  have hτ : (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB ∈ FilB P 1 := by
    rw [Algebra.smul_def]
    exact qB_mul_mem _ tD_mem
  have hv : P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) ∈ FilB P 0 := io_mem AI _
  have key := eval₂_sub_trunc_mem (ι : ↥LL.1 →+* P.R.BdR) hφ hτ m
    (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) hv ?_ p
  · rw [PowerSeries.eval₂_trunc_eq_sum_range] at key
    exact key
  rcases m with _ | m
  · exact sub_mem hv (eval₂_mem_zero _ hφ (FilB_anti zero_le_one hτ) _)
  have h := GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI T s 1 (m + 1)
  rw [map_sub (PowerSeries.trunc (m + 1)), PowerSeries.trunc_one, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, PowerSeries.eval₂_trunc_eq_sum_range, ← io_apply, map_sub, map_one,
    sub_sub_sub_cancel_right]
  rw [pow_one, pow_one, Finset.mul_sum] at h
  suffices hs : ∑ k ∈ Finset.range (m + 1), (ι : ↥LL.1 →+* P.R.BdR)
      (PowerSeries.coeff k (PowerSeries.C ζ * PowerSeries.exp ↥LL.1)) *
        ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k = ∑ k ∈ Finset.range (m + 1), oB P (P.ζQ s) *
          (qB P ((((1 : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ k / (k.factorial : ℚ_[l])) * tD P ^ k) by
    rw [hs]
    exact h
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ι (algebraMap ℚ ↥LL.1 (1 / (k.factorial : ℚ))) = qB P (1 / (k.factorial : ℚ_[l])) := by
    rw [← ι.commutes]
    congr 1
    simp
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_exp, map_mul, RingHom.coe_coe, hζ, hk,
    Algebra.smul_def, mul_pow, ← map_pow, mul_assoc, ← mul_assoc (qB P _), ← map_mul]
  congr 3
  simp [div_eq_mul_inv, mul_comm]

end GlobalTheory.ExpImage.PolyTaylor
