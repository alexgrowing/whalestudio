import Mathlib

noncomputable section

open MeasureTheory ValuativeRel

namespace PI.ProdFormulaE

open scoped Classical in

def modF (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    (a : K) : ℝ :=
  if h : a = 0 then 0 else ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ)

section

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

theorem modF_zero : modF K 0 = 0 := by
  unfold modF
  rw [dif_pos rfl]

theorem modF_of_ne {a : K} (h : a ≠ 0) :
    modF K a = ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ) := by
  unfold modF
  rw [dif_neg h]

theorem modF_pos {a : K} (h : a ≠ 0) : 0 < modF K a := by
  rw [modF_of_ne h]
  have hu : IsUnit (distribHaarChar K (Units.mk0 a h)) := (Group.isUnit (Units.mk0 a h)).map (distribHaarChar K)
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)

theorem modF_mul (a b : K) : modF K (a * b) = modF K a * modF K b := by
  by_cases ha : a = 0
  · subst ha; simp [modF_zero]
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb]
  have hu : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb := by
    ext; simp
  rw [hu, map_mul, NNReal.coe_mul]

theorem modF_one : modF K 1 = 1 := by
  rw [modF_of_ne one_ne_zero]
  have hu : Units.mk0 (1 : K) one_ne_zero = 1 := by
    ext; simp
  rw [hu, map_one, NNReal.coe_one]

theorem modF_div (a b : K) : modF K (a / b) = modF K a / modF K b := by
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  have hm : modF K (a / b) * modF K b = modF K a := by
    rw [← modF_mul, div_mul_cancel₀ a hb]
  rw [eq_div_iff (modF_pos hb).ne']
  exact hm

end

def IndexFormula : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (t : 𝒪[K]), t ≠ 0 →
      modF K (t : K) * (Nat.card (𝒪[K] ⧸ Ideal.span {t}) : ℝ) = 1

open IsDedekindDomain NumberField in

def CardStep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι → (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ (a : 𝓞 F), a ≠ 0 → ∀ t : 𝒪[K], (t : K) = ι (a : F) →
      Nat.card (𝒪[K] ⧸ Ideal.span {t}) = Ideal.absNorm (p.maxPowDividing (Ideal.span {a}))

end PI.ProdFormulaE
