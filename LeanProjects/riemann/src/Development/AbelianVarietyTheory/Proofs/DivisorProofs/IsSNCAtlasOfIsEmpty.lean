import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace GlobalTheory.SNCComp

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.LogResInt

variable {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def IsSNCAtlas (B : FinHolAtlas (n + 1) Y) (μ : Y → X) {q r : ℕ} (L : Fin q → LocPot X)
    (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) (k : Fin r)
    (C : FinHolAtlas n (W k)) : Prop :=
  ∀ j, ∃ (y : Y) (χ : OpenPartialHomeomorph Y (Fin (n + 1) → ℂ)) (κ : Fin r → Option (Fin (n + 1)))
      (a : Fin (n + 1)),
    IsCompatChart B χ ∧ y ∈ χ.source ∧ κ k = some a ∧
    (∀ k₁ k₂ b, κ k₁ = some b → κ k₂ = some b → k₁ = k₂) ∧
    (∀ k', W k' ∩ χ.source = {w ∈ χ.source | ∃ b, κ k' = some b ∧ χ w b = 0}) ∧
    (∀ i, χ.source ⊆ μ ⁻¹' (L i).U (μ y) ∧ ∃ u : Y → ℂ, B.HoloOn χ.source u ∧
        (∀ w ∈ χ.source, u w ≠ 0) ∧
        ∀ w ∈ χ.source, t i (μ y) (μ w) = u w * ∏ k', (match κ k' with
          | some b => χ w b ^ e i k'
          | none => 1)) ∧
    (C.chart j).source = Subtype.val ⁻¹' χ.source ∧
    (∀ w ∈ (C.chart j).source, C.chart j w = fun b => χ w.1 (a.succAbove b)) ∧
    (C.chart j).target = {z | Fin.insertNth a 0 z ∈ χ.target} ∧
    ∀ z ∈ (C.chart j).target, ((C.chart j).symm z).1 = χ.symm (Fin.insertNth a 0 z)

end GlobalTheory.SNCComp
