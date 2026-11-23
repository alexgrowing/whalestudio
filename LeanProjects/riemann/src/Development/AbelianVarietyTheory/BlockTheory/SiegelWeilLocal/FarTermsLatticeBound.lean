import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound

open Formalism.MainNotions.S GlobalTheory.Count

def farSet (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d ep x γ}

def latFactor (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / tau1 I x ^ 2) ^ (2 * (I.n ^ 2 * I.f))

def FarTermsBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h ep : ℝ),
    IsDSData B d → SigIs B p q → q = min p q → 1 ≤ q → 1 ≤ B.g → GapGe B h →
    0 < ep → ep ≤ 1 / Real.sqrt (2 * (q : ℝ)) → 2 * (B.I.n : ℝ) ^ 2 * ep ≤ Real.log 2 →
    64 * (B.I.n : ℝ) ^ 2 ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 → 8 * (B.I.n : ℝ) * (q : ℝ) < h →
    ∀ x : B.I.GA,
      Summable (fun γ : farSet B d ep x => ‖phe B d (x⁻¹ * γ.1 * x)‖) ∧
      ∑' γ : farSet B d ep x, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤
        (∏ v, d v) * (B.e 1).re * latFactor B.I x *
          (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * ep ^ 2 / 16)))

example (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x γ : B.I.GA) (hγ : γ ∈ B.I.GFset) :
    γ ∈ farSet B d ep x ↔
      (phe B d (x⁻¹ * γ * x) = 0 ∨ ∃ v, ep < dHS (uMat ((x⁻¹ * γ * x).1 v))) := by
  simp only [farSet, IsNear, Set.mem_setOf_eq, hγ, true_and, not_and_or, not_not, not_forall, not_le, ne_eq, not_true, false_or]

example : ∃ h ep : ℝ, 0 < ep ∧ ep ≤ 1 / Real.sqrt (2 * ((1 : ℕ) : ℝ)) ∧
    2 * ((2 : ℕ) : ℝ) ^ 2 * ep ≤ Real.log 2 ∧ 64 * ((2 : ℕ) : ℝ) ^ 2 ≤ h * ep ∧ 1 ≤ h * ep ^ 2 / 16 ∧
    8 * ((2 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) < h := by
  refine ⟨10000, 1 / 16, by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · have h1 : Real.sqrt (2 * ((1 : ℕ) : ℝ)) ≤ 16 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h2 : 0 < Real.sqrt (2 * ((1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by norm_num)
    exact one_div_le_one_div_of_le h2 h1
  · have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound
