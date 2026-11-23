import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Hol

theorem differentiable_ee : Differentiable ℂ ee := by
  unfold ee
  exact (differentiable_id.const_mul _).cexp

theorem differentiableOn_geomProd {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    DifferentiableOn ℂ (fun z => ∏' m : ℕ, (1 - ee z ^ (m + 1) * g z)) {z : ℂ | 0 < z.im} := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hec : Continuous ee := differentiable_ee.continuous
  have hgc : Continuous g := hg.continuous
  have hloc : HasProdLocallyUniformlyOn (fun (m : ℕ) (z : ℂ) => 1 + -(ee z ^ (m + 1) * g z))
      (fun z => ∏' m : ℕ, (1 + -(ee z ^ (m + 1) * g z))) {z : ℂ | 0 < z.im} := by
    refine hasProdLocallyUniformlyOn_of_forall_compact hU fun K hK hKc => ?_
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · subst hK0
      exact Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun _ => (0 : ℝ)) summable_zero
        (.of_forall fun n z hz => absurd hz (Set.notMem_empty z))
        (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne (continuous_norm.comp hec).continuousOn
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hgc.continuousOn
    set r := ‖ee z₀‖ with hr_def
    have hr1 : r < 1 := norm_ee_lt_one ⟨z₀, hK hz₀⟩
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr : ∀ z ∈ K, ‖ee z‖ ≤ r := fun z hz => hmax hz
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)
    refine Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun n => C * r * r ^ n)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (C * r)) (.of_forall fun n z hz => ?_)
      (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    rw [norm_neg, norm_mul, norm_pow]
    calc ‖ee z‖ ^ (n + 1) * ‖g z‖ ≤ r ^ (n + 1) * C :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hr z hz) _) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 _)
      _ = C * r * r ^ n := by ring
  have hd := hloc.differentiableOn (.of_forall fun n => by
    simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
      ((differentiable_const (1 : ℂ)).add ((differentiable_ee.pow (i + 1)).mul hg).neg).differentiableOn)) hU
  refine hd.congr fun z _ => ?_
  simp only [sub_eq_add_neg]

def geomProd (q a : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * a)

theorem tprod_cthFac {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ ≠ 0 ∧
    ∏' m : ℕ, cthFac c (ee τ) (ee (pt x τ)) (m + 1) =
      geomProd (ee τ) (ee (pt x τ)) ^ (c ^ 2) * geomProd (ee τ) (ee (pt x τ))⁻¹ ^ (c ^ 2) /
        (geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹) := by
  obtain ⟨hc1, hc6, hnot⟩ := h
  have hq : ‖ee τ‖ < 1 := norm_ee_lt_one τ
  have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact hnot ⟨⟨(c : ℤ) * a, by push_cast; rw [ha]⟩, ⟨(c : ℤ) * b, by push_cast; rw [hb]⟩⟩
  have hcx : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa [nsmul_eq_mul] using hnot
  have htc : ee (pt x τ) ^ c = ee (pt (c • x) τ) := ee_pt_pow c x τ
  have n1 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).1
  have n2 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ))⁻¹ ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).2
  have n3 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ^ c ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).1
  have n4 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ) ^ c)⁻¹ ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).2
  obtain ⟨P1, -, h1⟩ := hasProd_geom hq _ n1
  obtain ⟨P2, -, h2⟩ := hasProd_geom hq _ n2
  obtain ⟨P3, hP3, h3⟩ := hasProd_geom hq _ n3
  obtain ⟨P4, hP4, h4⟩ := hasProd_geom hq _ n4
  have e1 : geomProd (ee τ) (ee (pt x τ)) = P1 := h1.tprod_eq
  have e2 : geomProd (ee τ) (ee (pt x τ))⁻¹ = P2 := h2.tprod_eq
  have e3 : geomProd (ee τ) (ee (pt x τ) ^ c) = P3 := h3.tprod_eq
  have e4 : geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ = P4 := h4.tprod_eq
  rw [e1, e2, e3, e4]
  refine ⟨mul_ne_zero hP3 hP4, ?_⟩
  have hall := ((hasProd_pow h1 (c ^ 2)).mul (hasProd_pow h2 (c ^ 2))).mul
    (hasProd_inv (h3.mul h4) (mul_ne_zero hP3 hP4))
  rw [div_eq_mul_inv, ← hall.tprod_eq]
  refine tprod_congr fun m => ?_
  unfold cthFac
  rw [div_eq_mul_inv]

end GlobalTheory.Sieg.Hol

namespace GlobalTheory.Sieg

open Hol

theorem mdifferentiable_sg :
    ∀ (c : ℕ) (x : Fin 2 → ℚ), admitted c x → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sg c x) := by
  intro c x h
  rw [UpperHalfPlane.mdifferentiable_iff]
  set T : ℂ → ℂ := fun z => ee ((x 0 : ℂ) * z + (x 1 : ℂ)) with hT
  have hTd : Differentiable ℂ T := differentiable_ee.comp ((differentiable_id.const_mul _).add_const _)
  have hT0 : ∀ z, T z ≠ 0 := fun z => ee_ne_zero _
  have hG1 := differentiableOn_geomProd hTd
  have hG2 := differentiableOn_geomProd (hTd.inv hT0)
  have hG3 := differentiableOn_geomProd (hTd.pow c)
  have hG4 := differentiableOn_geomProd ((hTd.pow c).inv fun z => pow_ne_zero _ (hT0 z))
  have hnd : ∀ z ∈ {z : ℂ | 0 < z.im}, 1 - T z ^ c ≠ 0 := fun z hz =>
    (multipliable_and_sg_ne_zero h ⟨z, hz⟩).2.1
  have hnG : ∀ z ∈ {z : ℂ | 0 < z.im}, geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹ ≠ 0 :=
    fun z hz => (tprod_cthFac h ⟨z, hz⟩).1
  have hH : DifferentiableOn ℂ (fun z => ee z ^ ((c ^ 2 - 1) / 12) * (-T z) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (1 - T z) ^ (c ^ 2) / (1 - T z ^ c) *
      (geomProd (ee z) (T z) ^ (c ^ 2) * geomProd (ee z) (T z)⁻¹ ^ (c ^ 2) /
        (geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹))) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.mul (DifferentiableOn.div (DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_) ?_ hnd)
      (DifferentiableOn.div (DifferentiableOn.mul (hG1.pow _) (hG2.pow _)) (hG3.mul hG4) hnG)
    · exact (differentiable_ee.pow _).differentiableOn
    · exact hTd.neg.differentiableOn.zpow (Or.inl fun z _ => neg_ne_zero.mpr (hT0 z))
    · exact (((differentiable_const _).sub hTd).pow _).differentiableOn
    · exact ((differentiable_const _).sub (hTd.pow c)).differentiableOn
  refine hH.congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  unfold sg cth
  rw [(tprod_cthFac h ⟨z, hz'⟩).2]
  rfl

end GlobalTheory.Sieg
