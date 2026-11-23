import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.DegGrowth

open MvPolynomial

theorem expand (Ψ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Ψ ((X 0 + C t * X 1) ^ D) = ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  intro hC k _ Y _ p D hX L A
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).2
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  have hiso0 : (comb ![L, A] ![1, 0]).Isometric L := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, Fin.sum_univ_two]
  have hlin0 : (lin fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℝ)) = (X 0 : MvPolynomial (Fin 2) ℝ) := by
    simp [lin, Fin.sum_univ_two]
  have h0 : Ψ (X 0 ^ D) = gdeg L D := by
    rw [← hlin0, hΨ.1, hiso0.gdeg_eq]
  have hn_eq (n : ℕ) : gdeg ((L.pow n).tens A) D = Ψ ((C (n : ℝ) * X 0 + C 1 * X 1) ^ D) := by
    rw [← (hiso n).gdeg_eq, ← hΨ.1, hlin]
  set f : ℝ → ℝ := fun t => Ψ ((X 0 + C t * X 1) ^ D) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Ψ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = gdeg L D := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hn_eq, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.DegGrowth
