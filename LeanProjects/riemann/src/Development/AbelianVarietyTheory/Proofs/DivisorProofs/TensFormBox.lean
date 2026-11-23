import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

def tensForm {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ) : ((κ ⊕ κ' → k) → ℂ) →ₗ[ℂ] ℂ where
  toFun f := l₁ fun x₁ => l₂ fun x₂ => f (Sum.elim x₁ x₂)
  map_add' f g := by
    rw [← map_add]; congr 1; funext x₁; rw [Pi.add_apply, ← map_add]; rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; funext x₁; rw [Pi.smul_apply, ← map_smul]; rfl

theorem tensForm_box {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ)
    (φ₁ : (κ → k) → ℂ) (φ₂ : (κ' → k) → ℂ) : tensForm l₁ l₂ (boxFun φ₁ φ₂) = l₁ φ₁ * l₂ φ₂ := by
  have e : (fun x₁ => l₂ fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = l₂ φ₂ • φ₁ := by
    funext x₁
    have : (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := by funext x₂; rfl
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  change l₁ _ = _
  rw [e, map_smul, smul_eq_mul, mul_comm]

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def repl (v : Pl F) (y : κ → AF F) (x : κ → Fv F v) : κ → AF F :=
  fun i => y i - liftV v (evFin F v (y i)) + liftV v (x i)

def proj (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ y := φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x)
  map_add' Φ Ψ := by
    funext y
    rw [Pi.add_apply, ← mul_add, ← map_add]; rfl
  map_smul' c Φ := by
    funext y
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← smul_eq_mul c, ← map_smul]; rfl

theorem proj_apply (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (Φ : (κ → AF F) → ℂ)
    (y : κ → AF F) : proj v φ₀ l Φ y = φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x) := rfl

theorem evFin_repl (v : Pl F) (y : κ → AF F) (x : κ → Fv F v) (i : κ) : evFin F v (repl v y x i) = x i := by
  simp [repl, evFin_liftV]

theorem proj_tens (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (κ → Fv F v) → ℂ)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) :
    proj v φ₀ l (tens (evFin F v) φ r) = l φ • tens (evFin F v) φ₀ r := by
  funext y
  have e : (fun x => tens (evFin F v) φ r (repl v y x)) = r y • φ := by
    funext x
    have h1 : repl v y x = y + fun i => liftV v (x i - evFin F v (y i)) := by
      funext i; simp only [repl, Pi.add_apply, map_sub]; ring
    have h2 : r (repl v y x) = r y := by
      rw [h1]; exact hr _ _ fun u hu => funext fun i => at_liftV v _ u hu
    simp only [tens, evFin_repl, h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [proj_apply, e, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.MixedForm

end
