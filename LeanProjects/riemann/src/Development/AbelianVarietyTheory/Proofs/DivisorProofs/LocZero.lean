import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tens_inj (v : Pl F) {κ : Type} (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRt : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (e : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hRt 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

theorem acts_unique (v : Pl F) {κ : Type} [Fintype κ] (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  exact tens_inj v R hR0 (hR φ hφ).1 ((h₁ R (hR φ hφ)).symm.trans (h₂ R (hR φ hφ)))

section Grp
variable {n : ℕ} {W : Spc F E n}

theorem mat_mul (g h : UA σ W.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul (h : UA σ W.J) : mat h⁻¹ * mat h = 1 := by
  rw [← mat_mul, inv_mul_cancel]; rfl

theorem mat_one : mat (1 : UA σ W.J) = 1 := rfl

theorem uAt_mul (v : Pl F) {g h : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) (hh : h ∈ UAt σ W (evFin F v)) :
    g * h ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    rw [mat_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  show u • (mat (g * h) - 1) = 0
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem uAt_inv (v : Pl F) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) : h⁻¹ ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by
    rw [Matrix.mul_sub, mat_inv_mul, Matrix.mul_one]; abel
  show u • (mat h⁻¹ - 1) = 0
  rw [e, smul_neg, ← Matrix.mul_smul, hh u hu, Matrix.mul_zero, neg_zero]

end Grp

section Loc
variable {a a' : ℕ} {B : Base F E} (G : Geo σ a a') {X : Chars F E}

open Classical in

def loc (om : Rep σ G.V G.W) (v : Pl F) (h : UA σ G.W.J) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) :
    (Fin a × Fin (a + a') → Fv F v) → ℂ :=
  if hx : ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ then hx.choose else 0

variable {G} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem tens_add (v : Pl F) {κ : Type} (φ ψ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ) :
    tens (evFin F v) (φ + ψ) r = tens (evFin F v) φ r + tens (evFin F v) ψ r := by
  funext x; simp [tens, add_mul]

end Loc

end GlobalTheory.InertAvg
