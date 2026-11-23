import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallMid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (W₁) in

def JRel {d d₁ : ℕ} {W : Spc F E d} (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℂ) (χ' : Chr F E) (z' : ℂ)
    (T : UA σ W.J → ℂ) : Prop :=
  ∀ t t' m m', IsLevi (W₁ := W₁) H' t 1 m → IsLevi (W₁ := W₁) H' t' 1 m' → ∀ h,
    T (m' * (m * h)) - (χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z' * T (m * h) -
      (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * T (m' * h) +
      (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z') * T h = 0

example {d d₁ : ℕ} {W : Spc F E d} (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ χ' : Chr F E) (z z' : ℂ) :
    JRel (σ := σ) (W := W) W₁ H' χ z χ' z' 0 := fun _ _ _ _ _ _ _ => by simp

theorem exists_split {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ₃ χ₄ : Chr F E} {z₃ z₄ : ℂ}
    {T : UA σ W.J → ℂ} (h34 : JRel W₁ H' χ₃ z₃ χ₄ z₄ T) (h43 : JRel W₁ H' χ₄ z₄ χ₃ z₃ T) {t₀ : (AE F E)ˣ} {m₀ : UA σ W.J}
    (hm₀ : IsLevi (W₁ := W₁) H' t₀ 1 m₀)
    (hne : (χ₃ t₀ : ℂ) * ((absE F E t₀ : ℝ) : ℂ) ^ z₃ ≠ (χ₄ t₀ : ℂ) * ((absE F E t₀ : ℝ) : ℂ) ^ z₄) :
    ∃ T₃ T₄ : UA σ W.J → ℂ, T = T₃ + T₄ ∧ GlobalTheory.ConeSmallCT.HasLawC W₁ H' χ₃ z₃ T₃ ∧
      GlobalTheory.ConeSmallCT.HasLawC W₁ H' χ₄ z₄ T₄ := by
  set c₃ : ℂ := (χ₃ t₀ : ℂ) * ((absE F E t₀ : ℝ) : ℂ) ^ z₃ with hc₃
  set c₄ : ℂ := (χ₄ t₀ : ℂ) * ((absE F E t₀ : ℝ) : ℂ) ^ z₄ with hc₄
  have hD : c₃ - c₄ ≠ 0 := sub_ne_zero.2 hne
  refine ⟨fun h => (T (m₀ * h) - c₄ * T h) / (c₃ - c₄), fun h => (c₃ * T h - T (m₀ * h)) / (c₃ - c₄), ?_, ?_, ?_⟩
  · funext h
    simp only [Pi.add_apply]
    field_simp
    ring
  · intro t m hm h
    have e := h34 t t₀ m m₀ hm hm₀ h
    rw [← hc₄] at e
    rw [eq_comm, ← mul_div_assoc, div_left_inj' hD]
    linear_combination (-1 : ℂ) * e
  · intro t m hm h
    have e := h43 t t₀ m m₀ hm hm₀ h
    rw [← hc₃] at e
    rw [eq_comm, ← mul_div_assoc, div_left_inj' hD]
    linear_combination e

theorem ne_of_re_ne' {u v : Circle} {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {w w' : ℂ} (h : w.re ≠ w'.re) :
    (u : ℂ) * (r : ℂ) ^ w ≠ (v : ℂ) * (r : ℂ) ^ w' := by
  intro heq
  have hn := congrArg norm heq
  simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr] at hn
  apply h
  have hl := congrArg Real.log hn
  rw [Real.log_rpow hr, Real.log_rpow hr] at hl
  exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one hr hr1) hl

end GlobalTheory.ConeSmallMid

end
