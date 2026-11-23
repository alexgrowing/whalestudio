import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF.PhysicalTorus

variable {n : ℕ}

theorem prod_mode (ε : Fin n → Bool) {p : Fin n × Fin n → Prop} [Fintype (Subtype p)]
    (hp : ∀ x, p x ↔ ε x.1 = true ∧ ε x.2 = false) (f : Fin n × Fin n → ℂ) :
    ∏ x : Subtype p, f x.1 =
      ∏ i ∈ univ.filter (fun i => ε i = true), ∏ a ∈ univ.filter (fun a => ε a = false), f (i, a) := by
  rw [← Finset.prod_subtype ((univ.filter (fun i => ε i = true)) ×ˢ (univ.filter (fun a => ε a = false)))
    (fun x => by simp [hp, Finset.mem_product]) f, Finset.prod_product]

theorem physDet_diag (ε : Fin n → Bool) (s : Fin n → ℂ) :
    physDet ε (Matrix.diagonal s) = ∏ x : {x : Fin n × Fin n // IsPhys ε x}, (1 - s x.1.1 * star (s x.1.2)) := by
  rw [physDet, ← Matrix.det_diagonal]
  congr 1
  funext x y
  by_cases h : x = y
  · subst h; simp
  · have hxy : x.1.1 ≠ y.1.1 ∨ x.1.2 ≠ y.1.2 := by
      by_contra hc
      push Not at hc
      exact h (Subtype.ext (Prod.ext hc.1 hc.2))
    rcases hxy with h1 | h1 <;> simp [Matrix.diagonal_apply, h, h1]

theorem tor_ne (θ : Fin n → ℝ) (a : Fin n) : tor θ a ≠ 0 := Complex.exp_ne_zero _

theorem norm_tor (θ : Fin n → ℝ) (a : Fin n) : ‖tor θ a‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem star_tor (θ : Fin n → ℝ) (a : Fin n) : star (tor θ a) = (tor θ a)⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_tor]
  simp

theorem one_sub_tor (θ : Fin n → ℝ) (i a : Fin n) :
    1 - tor θ i * star (tor θ a) = -1 * (tor θ i - tor θ a) * (tor θ a)⁻¹ := by
  rw [star_tor]
  have h := mul_inv_cancel₀ (tor_ne θ a)
  linear_combination -h

theorem factor_tor (θ : Fin n → ℝ) (i a : Fin n) :
    (1 - tor θ i * star (tor θ a)) * conj (1 - tor θ i * star (tor θ a)) = ((‖tor θ i - tor θ a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, one_sub_tor, norm_mul, norm_mul, norm_inv, norm_tor]
  simp

end PhysicalTorus

open PhysicalTorus

theorem adjointDet_onCompactTorus : PhysTor := by
  intro n ε θ
  have hD : physDet ε (Matrix.diagonal (tor θ)) = ∏ i ∈ univ.filter (fun i => ε i = true),
      ∏ a ∈ univ.filter (fun a => ε a = false), (1 - tor θ i * star (tor θ a)) := by
    rw [physDet_diag]
    exact prod_mode ε (p := IsPhys ε) (fun _ => Iff.rfl) (fun y => 1 - tor θ y.1 * star (tor θ y.2))
  have hM : ∀ f : Fin n × Fin n → ℂ, ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, f x.1 = ∏ i ∈ univ.filter (fun i => ε i = true),
      ∏ a ∈ univ.filter (fun a => ε a = false), f (i, a) := fun f => prod_mode ε (fun _ => Iff.rfl) f
  refine ⟨?_, ?_⟩
  · have hV : ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2) = ∏ i ∈ univ.filter (fun i => ε i = true),
        ∏ a ∈ univ.filter (fun a => ε a = false), (tor θ i - tor θ a) := hM (fun y => tor θ y.1 - tor θ y.2)
    have hS : (-1 : ℂ) ^ (pOf ε * qOf ε) = ∏ i ∈ univ.filter (fun i => ε i = true),
        ∏ a ∈ univ.filter (fun a => ε a = false), (-1 : ℂ) := by
      rw [Finset.prod_const, Finset.prod_const, ← pow_mul, mul_comm, pOf, qOf]
    have hR : ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) = ∏ i ∈ univ.filter (fun i => ε i = true),
        ∏ a ∈ univ.filter (fun a => ε a = false), (tor θ a)⁻¹ := by
      rw [Finset.prod_comm]
      simp only [Finset.prod_const]
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun a _ => ?_
      cases h : ε a <;> simp [pOf, zpow_neg, inv_pow]
    rw [hD, hV, hS, hR]
    simp only [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun a _ => one_sub_tor θ i a
  · rw [hD, map_prod]
    simp only [map_prod, ← Finset.prod_mul_distrib, factor_tor]
    rw [GlobalTheory.PsCo.Pc1.dMode, Complex.ofReal_prod]
    exact (hM (fun y => ((‖tor θ y.1 - tor θ y.2‖ ^ 2 : ℝ) : ℂ))).symm

end GlobalTheory.PsCo.PcEF

end
