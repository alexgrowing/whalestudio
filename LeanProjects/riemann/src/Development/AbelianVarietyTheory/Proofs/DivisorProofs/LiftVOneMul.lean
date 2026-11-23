import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvgDual

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : Pl F) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

section Local

variable {F : Type} [Field F] [NumberField F]

theorem eq_of_tens_eq {κ : Type} [Fintype κ] (v : Pl F) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hRv : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hR : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by simpa using hRv 0 _ hat
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_unique {κ : Type} [Fintype κ] (v : Pl F) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hR : ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ R) (T : Module.End ℂ ((κ → AF F) → ℂ))
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  exact eq_of_tens_eq v hR0 (hR φ hφ).1 ((h₁ R (hR φ hφ)).symm.trans (h₂ R (hR φ hφ)))

theorem acts_one {κ : Type} [Fintype κ] (v : Pl F) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (1 : Module.End ℂ ((κ → AF F) → ℂ)) φ φ := fun _ _ => rfl

theorem acts_comp {κ : Type} [Fintype κ] (v : Pl F) (T S : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) S φ₁ φ₂) : Acts (evFin F v) (S * T) φ φ₂ := by
  intro r hr
  have e := h₁ r hr
  have hr' : Rest (evFin F v) φ₁ r := ⟨hr.1, e ▸ hT _ hr.2⟩
  rw [Module.End.mul_apply, e]
  exact h₂ r hr'

end Local

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Stab

end GlobalTheory.InertAvgDual
