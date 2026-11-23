import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dH (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  fun x => deriv (fun t : ℝ => schr ψ (realAd F t • w) Φ x) 0

def wordH (ψ : AddChar (AF F) ℂ) (l : List ((κ → AF F) × (κ → AF F))) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  l.foldr (dH ψ) Φ

def IsArch (w : (κ → AF F) × (κ → AF F)) : Prop :=
  ∀ i, At (evI F) (w.1 i) ∧ At (evI F) (w.2 i)

open scoped Classical in

def IsArchUnit (w : (κ → AF F) × (κ → AF F)) : Prop :=
  IsArch w ∧ ∀ i, ‖evI F (w.1 i)‖ ≤ 1 ∧ ‖evI F (w.2 i)‖ ≤ 1

@[simp] theorem wordH_nil (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : wordH ψ [] Φ = Φ := rfl

theorem wordH_cons (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (l : List ((κ → AF F) × (κ → AF F)))
    (Φ : (κ → AF F) → ℂ) : wordH ψ (w :: l) Φ = dH ψ w (wordH ψ l Φ) := rfl

theorem dH_smul (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (a : ℂ) (Φ : (κ → AF F) → ℂ) :
    dH ψ w (a • Φ) = a • dH ψ w Φ := by
  funext x
  simp only [dH, schr, Pi.smul_apply, smul_eq_mul]
  have : (fun t : ℝ => ψ (x ⬝ᵥ (realAd F t • w).2 + ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2)) *
      (a * Φ (x + (realAd F t • w).1))) = fun t => a * (ψ (x ⬝ᵥ (realAd F t • w).2 +
      ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2)) * Φ (x + (realAd F t • w).1)) := by
    funext t; ring
  rw [this, deriv_const_mul_field']

theorem realAd_mul (a b : ℝ) : realAd F a * realAd F b = realAd F (a * b) := by
  unfold realAd
  simp only [LinearMap.inl_apply, map_mul]
  refine Prod.ext ?_ ?_
  · show _ * _ = _
    rw [← map_mul]
  · exact mul_zero _

theorem dH_realAd_smul (ψ : AddChar (AF F) ℂ) (c : ℝ) (w : (κ → AF F) × (κ → AF F)) (Φ : (κ → AF F) → ℂ) :
    dH ψ (realAd F c • w) Φ = (c : ℂ) • dH ψ w Φ := by
  funext x
  simp only [dH, Pi.smul_apply, smul_eq_mul]
  have e : (fun t : ℝ => schr ψ (realAd F t • realAd F c • w) Φ x) =
      fun t => (fun s : ℝ => schr ψ (realAd F s • w) Φ x) (c * t) := by
    funext t; rw [smul_smul, realAd_mul, mul_comm t c]
  rw [e]
  have h := deriv_comp_mul_left (f := fun s : ℝ => schr ψ (realAd F s • w) Φ x) (c := c) (x := 0)
  rw [mul_zero, Complex.real_smul] at h
  exact h

theorem isArch_smul {w : (κ → AF F) × (κ → AF F)} (hw : IsArch w) (a : AF F) : IsArch (a • w) := by
  intro i
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · show u * (a * w.1 i) = 0
    rw [mul_left_comm]
    have := (hw i).1 u hu
    simp only [smul_eq_mul] at this
    rw [this, mul_zero]
  · show u * (a * w.2 i) = 0
    rw [mul_left_comm]
    have := (hw i).2 u hu
    simp only [smul_eq_mul] at this
    rw [this, mul_zero]

end GlobalTheory.ThetaDecay

end
