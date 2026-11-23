import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.mul_powerSeries {N : ℕ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
    (hf : HasQ N f (fun n => PowerSeries.coeff n φ)) (hg : HasQ N g (fun n => PowerSeries.coeff n ψ)) :
    HasQ N (fun τ => f τ * g τ) (fun n => PowerSeries.coeff n (φ * ψ)) := by
  have h := hf.mul_conv hg
  have e : conv (fun n => PowerSeries.coeff n φ) (fun n => PowerSeries.coeff n ψ) =
      fun n => PowerSeries.coeff n (φ * ψ) := by
    funext n; rw [conv, PowerSeries.coeff_mul]
  rwa [e] at h

theorem HasQ.pow_powerSeries {N : ℕ} {f : ℍ → ℂ} {b : ℕ → ℂ} (hf : HasQ N f b) (i : ℕ) :
    HasQ N (fun τ => f τ ^ i) (fun n => PowerSeries.coeff n (PowerSeries.mk b ^ i)) := by
  induction i with
  | zero =>
    have h := HasQ.const N (1 : ℂ)
    convert h using 2 <;> simp [PowerSeries.coeff_one]
  | succ i ih =>
    have hb : HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk b)) := by
      simpa only [PowerSeries.coeff_mk] using hf
    have h := ih.mul_powerSeries hb
    simpa only [pow_succ] using h

theorem polyRel_qSeries : ∀ (N n : ℕ) (f : ℍ → ℂ) (b : ℕ → ℂ) (p : ℕ → ℍ → ℂ) (c : ℕ → ℕ → ℂ), 0 < N → HasQ N f b → (∀ i, HasQ N (p i) (c i)) → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i = 0) → (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i))).eval (PowerSeries.mk b) = 0 := by
  intro N n f b p c hN hf hp hrel
  have hterm : ∀ i ∈ Finset.range (n + 1), HasQ N (fun τ => p i τ * f τ ^ i)
      (fun m => PowerSeries.coeff m (PowerSeries.mk (c i) * PowerSeries.mk b ^ i)) := by
    intro i _
    have hpi : HasQ N (p i) (fun m => PowerSeries.coeff m (PowerSeries.mk (c i))) := by
      simpa only [PowerSeries.coeff_mk] using hp i
    exact hpi.mul_powerSeries (hf.pow_powerSeries i)
  have hsum := HasQ.sum (Finset.range (n + 1)) hterm
  have hzero : HasQ N (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) (fun _ => 0) := by
    have h0 := HasQ.const N (0 : ℂ)
    have e : (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) = fun _ => (0 : ℂ) :=
      funext hrel
    rw [e]
    simpa using h0
  have hc := HasQ.coeff_unique hN hsum hzero
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  ext m
  have := congrFun hc m
  simpa [map_sum] using this

end GlobalTheory.QFam
