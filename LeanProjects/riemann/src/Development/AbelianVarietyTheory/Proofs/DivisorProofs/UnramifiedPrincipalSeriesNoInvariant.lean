import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesZeroOfCoordinateZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesCoordinateNearInfinityStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

theorem isUnram_mul {χ ψ : kˣ →* ℂˣ} (h : IsUnram χ) (h' : IsUnram ψ) : IsUnram (χ * ψ) := fun x hx => by
  rw [MonoidHom.mul_apply, h x hx, h' x hx, one_mul]

theorem bchar_shift (μ₁ μ₂ : kˣ →* ℂˣ) (a d t : kˣ) :
    bchar μ₁ μ₂ (a * t) (d * t⁻¹) = bchar μ₁ μ₂ a d * ((μ₁ t * absPow k 1 t / μ₂ t : ℂˣ) : ℂ) := by
  have h1 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by rw [← absPow_add]; norm_num
  have h2 : absPow k (-1 / 2) = (absPow k (1 / 2))⁻¹ := by rw [neg_div, absPow_neg]
  simp only [bchar, h1, h2, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
  have e1 : ((μ₂ t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e2 : ((absPow k (1 / 2) d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e3 : ((absPow k (1 / 2) t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem val_lt_val_mul_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : kˣ) :
    valuation k (y : k) < valuation k ((y * ϖ⁻¹ : kˣ) : k) := by
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hy0 : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
  have hϖ0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  exact lt_mul_of_one_lt_right hy0 ((one_lt_inv₀ hϖ0).2 hu)

end GlobalTheory.PrinTwo.NoFix

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_zero_of_fixed_of
    (hinj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0)
    (hasy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1)
    {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂) (hne : μ₂ ≠ μ₁ * absPow k 1)
    (f : PSp μ₁ μ₂) (hf : ∀ x : k, psRep μ₁ μ₂ (nU x) f = f) : f = 0 := by
  have hc : ∀ x : k, coord f x = ev f wE := fun x => by
    rw [coord, ← ev_act, hf x]
  obtain ⟨R, hR⟩ := hasy k μ₁ μ₂ f
  obtain ⟨ϖ, hϖ⟩ := exists_unif k
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x = R * ϖ⁻¹ := ⟨_, rfl⟩
  have hxR : valuation k (R : k) < valuation k (x : k) := hx ▸ val_lt_val_mul_inv hϖ R
  have hx'R : valuation k (R : k) < valuation k ((x * ϖ⁻¹ : kˣ) : k) :=
    hxR.trans (val_lt_val_mul_inv hϖ x)
  have h1 : ev f 1 = 0 := by
    by_contra h0
    apply hne
    have e := (hR x hxR).symm.trans ((hc x).trans ((hc _).symm.trans (hR _ hx'R)))
    have e2 : bchar μ₁ μ₂ (-(x * ϖ⁻¹)⁻¹) (x * ϖ⁻¹) =
        bchar μ₁ μ₂ (-x⁻¹) x * ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) := by
      rw [← bchar_shift]
      congr 1
      rw [mul_inv_rev, inv_inv, neg_mul, mul_comm]
    rw [e2, mul_assoc] at e
    have e3 := mul_left_cancel₀ (bchar_ne_zero μ₁ μ₂ _ _) e
    have e4 : ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e3.symm.trans (one_mul _).symm)
      exact this
    have e5 : μ₂ ϖ = (μ₁ * absPow k 1) ϖ := by
      rw [MonoidHom.mul_apply]
      exact (div_eq_one.1 (Units.ext e4)).symm
    rw [eq_unrChar h₂ hϖ, eq_unrChar (isUnram_mul h₁ (isUnram_absPow k 1)) hϖ, e5]
  refine hinj k μ₁ μ₂ f h1 fun y => ?_
  rw [hc y, ← hc x, hR x hxR, h1, mul_zero]

end GlobalTheory.PrinTwo.NoFix

theorem GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0 :=
  fun _ _ _ _ _ _ _ h₁ h₂ hne f hf =>
    GlobalTheory.PrinTwo.NoFix.eq_zero_of_fixed_of GlobalTheory.T.principal_series_zero_of_coordinate_zero GlobalTheory.T.principal_series_coordinate_near_infinity h₁ h₂ hne f hf
