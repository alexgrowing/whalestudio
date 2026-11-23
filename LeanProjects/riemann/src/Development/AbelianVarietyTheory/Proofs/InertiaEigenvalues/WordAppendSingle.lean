import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Growth (F : GA E a → ℂ) : Prop :=
  ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

def Good (F : GA E a → ℂ) : Prop :=
  ∃ h : F ∈ Sm E a, ∀ l : List (Lie E a),
    GlobalTheory.ShortVecDecay.Decays (GlobalTheory.GLFin.word l ⟨F, h⟩).1 ∧ Growth (GlobalTheory.GLFin.word l ⟨F, h⟩).1

variable (E a) in

def ccSpan : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (r : ℕ) (f : SchwartzMap (Fin a → Cinf E) ℂ) (G : GA E a → ℂ),
    Good G ∧ F = GlobalTheory.JSW.colConv r f G}

theorem Growth.zero : Growth (0 : GA E a → ℂ) := fun _ => ⟨0, 0, fun _ => by simp⟩

theorem Growth.add {F G : GA E a → ℂ} (hF : Growth F) (hG : Growth G) : Growth (F + G) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  obtain ⟨C', N', h'⟩ := hG g
  refine ⟨|C| + |C'|, max N N', fun y => ?_⟩
  have h1 := one_le_height y
  have p1 : height y ^ N ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_left _ _)
  have p2 : height y ^ N' ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_right _ _)
  have q : 0 ≤ height y ^ N := by positivity
  have q' : 0 ≤ height y ^ N' := by positivity
  calc ‖(F + G) (g * infGL E a y)‖ ≤ ‖F (g * infGL E a y)‖ + ‖G (g * infGL E a y)‖ := norm_add_le _ _
    _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h y) (h' y)
    _ ≤ |C| * height y ^ max N N' + |C'| * height y ^ max N N' := by
        exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C) q).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))) ((mul_le_mul_of_nonneg_right (le_abs_self C') q').trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C')))
    _ = (|C| + |C'|) * height y ^ max N N' := by ring

theorem Growth.smul {F : GA E a → ℂ} (hF : Growth F) (z : ℂ) : Growth (z • F) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  refine ⟨‖z‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem Good.mem_Sm {F : GA E a → ℂ} (h : Good F) : F ∈ Sm E a := h.1

theorem Good.decays {F : GA E a → ℂ} (h : Good F) : GlobalTheory.ShortVecDecay.Decays F := (h.2 []).1

theorem Good.growth {F : GA E a → ℂ} (h : Good F) : Growth F := (h.2 []).2

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by
  simp [GlobalTheory.GLFin.word, Module.End.mul_apply]

theorem word_append_single (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.prod_append, Module.End.mul_apply]

theorem Good.derivative {F : GA E a → ℂ} (h : Good F) (X : Lie E a) : Good (lieD X F) := by
  obtain ⟨hF, hl⟩ := h
  refine ⟨lieD_mem_Sm X hF, fun l => ?_⟩
  have e : (⟨lieD X F, lieD_mem_Sm X hF⟩ : Sm E a) = lie E a X ⟨F, hF⟩ := rfl
  rw [e, ← word_append_single]
  exact hl _

theorem good_zero : Good (0 : GA E a → ℂ) := by
  refine ⟨zero_mem _, fun l => ?_⟩
  have e : (⟨0, zero_mem _⟩ : Sm E a) = 0 := rfl
  rw [e, map_zero]
  exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩

theorem Good.add {F G : GA E a → ℂ} (hF : Good F) (hG : Good G) : Good (F + G) := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  refine ⟨add_mem hF1 hG1, fun l => ?_⟩
  have e : (⟨F + G, add_mem hF1 hG1⟩ : Sm E a) = ⟨F, hF1⟩ + ⟨G, hG1⟩ := rfl
  rw [e, map_add, Submodule.coe_add]
  exact ⟨(hF2 l).1.add (hG2 l).1, (hF2 l).2.add (hG2 l).2⟩

theorem Good.smul {F : GA E a → ℂ} (hF : Good F) (z : ℂ) : Good (z • F) := by
  obtain ⟨hF1, hF2⟩ := hF
  refine ⟨Submodule.smul_mem _ z hF1, fun l => ?_⟩
  have e : (⟨z • F, Submodule.smul_mem _ z hF1⟩ : Sm E a) = z • ⟨F, hF1⟩ := rfl
  rw [e, map_smul, Submodule.coe_smul]
  exact ⟨(hF2 l).1.smul z, (hF2 l).2.smul z⟩

theorem good_of_mem {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ π.V) : Good φ.1 :=
  ⟨φ.2, fun l => ⟨GlobalTheory.ShortVecDecay.decays_of_mem hπ (GlobalTheory.ShortVecDecay.word_mem l hφ),
    (π.cusp _ (GlobalTheory.ShortVecDecay.word_mem l hφ)).1.growth⟩⟩

end GlobalTheory.MSpanDecay
