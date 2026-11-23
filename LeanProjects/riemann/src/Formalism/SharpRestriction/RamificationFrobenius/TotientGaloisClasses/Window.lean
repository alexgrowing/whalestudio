import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

noncomputable section

namespace Formalism.HC

def HasWindows (S : Set ℝ) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ S

theorem HasWindows.mono {S S' : Set ℝ} {la x0 : ℝ} (h : HasWindows S la) (hS : ∀ x ≥ x0, x ∈ S → x ∈ S') :
    HasWindows S' la := by
  intro y
  obtain ⟨Y, hyY, hY⟩ := h (max y x0)
  exact ⟨Y, (le_max_left _ _).trans hyY,
    fun x h1 h2 => hS x ((le_max_right _ _).trans (hyY.trans h1)) (hY x h1 h2)⟩

theorem hasWindows_of_large {S : Set ℝ} {x0 : ℝ} (h : ∀ x ≥ x0, x ∈ S) (la : ℝ) : HasWindows S la :=
  fun y => ⟨max y x0, le_max_left _ _, fun x h1 _ => h x ((le_max_right _ _).trans h1)⟩

namespace Level

variable (Λ : Level)

def LandauWinAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → (∃ ψ ∈ Λ.KEPT, ∃ s : ℂ, θ < s.re ∧ DirichletCharacter.LFunction ψ.χ s = 0) →
    ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∃ y : ℝ, Y ≤ y ∧ y ≤ Y ^ la ∧ y ^ θ < Λ.Gm y

def LandauWin : Prop := ∀ la : ℝ, 1 < la → Λ.LandauWinAt la

def FormBAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ

def FormB : Prop := ∀ la : ℝ, 1 < la → Λ.FormBAt la

variable {Λ}

theorem FormBAt.mono {la la' : ℝ} (h : Λ.FormBAt la) (hl : la ≤ la') : Λ.FormBAt la' := by
  unfold FormBAt at h ⊢
  intro θ h0 h1 hw
  apply h θ h0 h1
  intro y
  obtain ⟨Y, hyY, hY⟩ := hw (max y 1)
  refine ⟨Y, (le_max_left _ _).trans hyY, fun x hx1 hx2 => hY x hx1 (hx2.trans ?_)⟩
  exact Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hyY) hl

end Level

end Formalism.HC

end
