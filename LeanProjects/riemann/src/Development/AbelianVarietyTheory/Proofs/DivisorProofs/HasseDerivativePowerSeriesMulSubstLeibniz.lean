import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse

open Polynomial

namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

theorem hasse_coe (l : ℕ) (f : R[X]) :
    hasse l (f : PowerSeries R) = ((hasseDeriv l f : R[X]) : PowerSeries R) := by
  ext n
  rw [coeff_hasse, Polynomial.coeff_coe, Polynomial.coeff_coe, hasseDeriv_coeff]

theorem coeff_hasse_congr {l n : ℕ} {φ φ' : PowerSeries R}
    (h : ∀ m ≤ n + l, PowerSeries.coeff m φ = PowerSeries.coeff m φ') :
    PowerSeries.coeff n (hasse l φ) = PowerSeries.coeff n (hasse l φ') := by
  rw [coeff_hasse, coeff_hasse, h _ le_rfl]

theorem coeff_mul_congr {n : ℕ} {φ φ' ψ ψ' : PowerSeries R}
    (h₁ : ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m φ')
    (h₂ : ∀ m ≤ n, PowerSeries.coeff m ψ = PowerSeries.coeff m ψ') :
    PowerSeries.coeff n (φ * ψ) = PowerSeries.coeff n (φ' * ψ') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h₁ _ (by omega), h₂ _ (by omega)]

theorem hasse_mul (l : ℕ) (φ ψ : PowerSeries R) :
    hasse l (φ * ψ) = ∑ p ∈ Finset.range (l + 1), hasse p φ * hasse (l - p) ψ := by
  ext n
  set M := n + l + 1 with hM
  set f : R[X] := PowerSeries.trunc M φ
  set g : R[X] := PowerSeries.trunc M ψ
  have hf : ∀ m < M, PowerSeries.coeff m φ = PowerSeries.coeff m (f : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hg : ∀ m < M, PowerSeries.coeff m ψ = PowerSeries.coeff m (g : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hpoly : hasse l ((f : PowerSeries R) * (g : PowerSeries R)) =
      ∑ p ∈ Finset.range (l + 1), hasse p (f : PowerSeries R) * hasse (l - p) (g : PowerSeries R) := by
    rw [← Polynomial.coe_mul, hasse_coe, hasseDeriv_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => hasseDeriv i f * hasseDeriv j g) l]
    simp only [hasse_coe]
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul]
  rw [coeff_hasse_congr (φ' := (f : PowerSeries R) * (g : PowerSeries R)), hpoly, map_sum, map_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpl : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    apply coeff_mul_congr
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hf m' (by omega)).symm
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hg m' (by omega)).symm
  · intro m hm
    exact coeff_mul_congr (fun m' hm' => hf m' (by omega)) (fun m' hm' => hg m' (by omega))

end GlobalTheory.PicDiv

namespace GlobalTheory

theorem hasse_mul_subst :
    ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
      ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) =
        ∑ p ∈ Finset.range (l + 1),
          ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  intro k _ a φ ψ l ha
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [GlobalTheory.PicDiv.hasse_mul, ← PowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul]

end GlobalTheory
