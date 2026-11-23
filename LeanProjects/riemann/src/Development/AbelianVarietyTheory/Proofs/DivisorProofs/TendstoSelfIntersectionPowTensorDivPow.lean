import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.SelfInterGrowth

open MvPolynomial

theorem expand (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Φ ((X 0 + C t * X 1) ^ (D + 1)) = ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (a : ℝ), L.IsSelfInter a → ∃ α : ℕ → ℝ, (∀ n, ((L.pow n).tens A).IsSelfInter (α n)) ∧ Tendsto (fun n : ℕ => α n / (n : ℝ) ^ (D + 1)) atTop (𝓝 a) := by
  intro hC k _ Y _ p D hX L A a ha
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).1
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  refine ⟨fun n => Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)), fun n => ?_, ?_⟩
  · exact (hiso n).isSelfInter hX (hΦ.1 _)
  have h0 : Φ (X 0 ^ (D + 1)) = a :=
    HermLB.IsSelfInter.unique hX ((((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1 0)) ha
  set f : ℝ → ℝ := fun t => Φ ((X 0 + C t * X 1) ^ (D + 1)) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Φ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = a := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)) / (n : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hlin, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.SelfInterGrowth
