import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt

noncomputable section

open NumberField

namespace GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def hmon (n : ℤ) (z : ℂ) : ℂ := if 0 ≤ n then (starRingEnd ℂ z) ^ n.toNat else z ^ (-n).toNat

def gauss (n : I → ℤ) (w : I → ℂ) : ℂ :=
  ∏ i, hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)

def dil (y : I → ℝ) (v : I → ℂ) : I → ℂ := fun i => (Real.exp (y i / 2) : ℂ) * v i

def theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (y : I → ℝ) : ℂ :=
  ∑' j, a j * gauss n (dil y (e j))

def emb {K : Type} [Field K] (φ : I → K →+* ℂ) (α : K) : I → ℂ := fun i => φ i α

def ulog {K : Type} [Field K] [NumberField K] (φ : I → K →+* ℂ) (u : (𝓞 K)ˣ) : I → ℝ :=
  fun i => Real.log (‖φ i ((u : 𝓞 K) : K)‖ ^ 2)

theorem hmon_zero {n : ℤ} (hn : n ≠ 0) : hmon n 0 = 0 := by
  unfold hmon
  split_ifs with h
  · rw [map_zero]; exact zero_pow (by omega)
  · exact zero_pow (by omega)

theorem gauss_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) : gauss n 0 = 0 := by
  obtain ⟨i, hi⟩ := hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hmon_zero hi])

theorem norm_hmon (n : ℤ) (z : ℂ) : ‖hmon n z‖ = ‖z‖ ^ n.natAbs := by
  unfold hmon
  split_ifs with h
  · rw [norm_pow, Complex.norm_conj]; congr 1; omega
  · rw [norm_pow]; congr 1; omega

end GlobalTheory.HeckeTheta
