import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def hk (s : ℝ) (w : ℂ) : ℂ := (w ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)

def hkInt (τ : ℂ) (s : ℝ) (n : ℤ) : ℂ := ∫ x : ℝ, hk s ((x : ℂ) + (n : ℂ) * τ)

def hkCell (τ : ℂ) (s : ℝ) (p : ℤ × ℤ) : ℂ :=
  hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ)
    - ∫ x in (0 : ℝ)..1, hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ)

def hkJ (a : ℝ) : ℝ := ∫ t : ℝ, (1 + t ^ 2) ^ (-a)

def HkSummable : Prop :=
  ∀ (τ : ℂ) (s : ℝ), τ.im ≠ 0 → 0 < s →
    Summable (fun p : ℤ × ℤ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ))

def HkRowIntegral : Prop :=
  ∀ (τ : ℂ) (s : ℝ) (n : ℤ), τ.im ≠ 0 → 0 ≤ s → n ≠ 0 →
    MeasureTheory.Integrable (fun x : ℝ => hk s ((x : ℂ) + (n : ℂ) * τ)) ∧
    HasSum (fun m : ℤ => ∫ x in (0 : ℝ)..1, hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)) (hkInt τ s n)

def HkCellBound : Prop :=
  ∀ τ : ℂ, τ.im ≠ 0 → ∃ b : ℤ × ℤ → ℝ, Summable b ∧
    ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p

def HkCellCont : Prop :=
  ∀ (τ : ℂ) (p : ℤ × ℤ), τ.im ≠ 0 → p.2 ≠ 0 →
    Filter.Tendsto (fun s : ℝ => hkCell τ s p) (nhdsWithin 0 (Set.Ioi 0)) (nhds (hkCell τ 0 p))

def HkIntZero : Prop := ∀ (τ : ℂ) (n : ℤ), τ.im ≠ 0 → n ≠ 0 → hkInt τ 0 n = 0

def HkIntValue : Prop :=
  ∀ (τ : ℂ) (s : ℝ) (n : ℤ), τ.im ≠ 0 → 0 < s → n ≠ 0 →
    hkInt τ s n = (((|(n : ℝ)| * |τ.im|) ^ (-(1 + 2 * s)) * (hkJ (1 + s) - 2 * hkJ (2 + s)) : ℝ) : ℂ)

def HkJRules : Prop :=
  (∀ a : ℝ, 1 / 2 < a → hkJ (a + 1) = (2 * a - 1) / (2 * a) * hkJ a) ∧ hkJ 1 = Real.pi ∧
  Filter.Tendsto (fun s : ℝ => hkJ (1 + s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi)

def HkRowZero : Prop :=
  Filter.Tendsto (fun s : ℝ => ∑' m : ℤ, hk s (m : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∑' m : ℤ, 1 / (m : ℂ) ^ 2))

def HkIntLimit : Prop :=
  ∀ τ : ℂ, τ.im ≠ 0 →
    (∀ s : ℝ, 0 < s → Summable (fun n : ℤ => if n = 0 then 0 else hkInt τ s n)) ∧
    Filter.Tendsto (fun s : ℝ => ∑' n : ℤ, if n = 0 then 0 else hkInt τ s n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-((Real.pi / |τ.im| : ℝ) : ℂ)))

def HkLimit : Prop :=
  ∀ τ : ℂ, τ.im ≠ 0 →
    Filter.Tendsto (fun s : ℝ => ∑' p : ℤ × ℤ, hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2) - ((Real.pi / |τ.im| : ℝ) : ℂ)))

end Formalism.L2.Th1.F
