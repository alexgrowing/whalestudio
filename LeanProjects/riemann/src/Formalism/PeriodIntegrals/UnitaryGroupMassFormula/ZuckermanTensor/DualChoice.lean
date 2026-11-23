import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualDefs

open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

section Sub
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cjSub (S : Submodule ℂ H) : Submodule ℂ (Cj H) where
  carrier := {x | Cj.un x ∈ S}
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun c _ hx => S.smul_mem ((starRingEnd ℂ) c) hx

def cjSubInv (S : Submodule ℂ (Cj H)) : Submodule ℂ H where
  carrier := {x | Cj.mk x ∈ S}
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun c x hx => by
    have h : (starRingEnd ℂ) c • Cj.mk x ∈ S := S.smul_mem ((starRingEnd ℂ) c) hx
    have e : (starRingEnd ℂ) c • Cj.mk x = Cj.mk (c • x) := by
      show (starRingEnd ℂ) ((starRingEnd ℂ) c) • x = c • x
      rw [Complex.conj_conj]
    show Cj.mk (c • x) ∈ S
    rw [← e]
    exact h

end Sub

def HCRev : Prop := ∀ (n : ℕ) (lam : Fin n → ℝ), IsHCParam lam → IsHCParam (revP lam)

def GapRev : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), GapAtLeast ε lam h → GapAtLeast (revE ε) (revP lam) h

def LowKRev : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), lowK (revE ε) (revP lam) = revP (lowK ε lam)

def VNormRev : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (ν : Fin n → ℝ), vNormSq (revE ε) (revP ν) = vNormSq ε ν

def CDomRev : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ Λ : Fin n → ℝ), CDom ε μ Λ → CDom (revE ε) (revP μ) (revP Λ)

def URepConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsURepOn (UJset (revE ε)) (sigC σ)

def IrredConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrredOn (UJset ε) σ → IsIrredOn (UJset (revE ε)) (sigC σ)

def SqIntConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntOn ε σ → IsSqIntOn (revE ε) (sigC σ)

def KTypeConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H),
    IsKTypeOf ε σ Λ S → IsKTypeOf (revE ε) (sigC σ) (revP Λ) (cjSub S)

def KTypeConjInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ (Cj H)),
    IsKTypeOf (revE ε) (sigC σ) Λ S → IsKTypeOf ε σ (revP Λ) (cjSubInv S)

def KFinConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), IsKFin ε σ v ↔ IsKFin (revE ε) (sigC σ) (Cj.mk v)

def DSConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsDS ε lam σ → IsDS (revE ε) (revP lam) (sigC σ)

theorem dualWeight_dualWeight {n : ℕ} (lam : Fin n → ℝ) : revP (revP lam) = lam := by
  funext a; simp [revP]

theorem revE_revE {n : ℕ} (ε : Fin n → Bool) : revE (revE ε) = ε := by
  funext a; simp [revE]

theorem dsConj_of (h1 : URepConj) (h2 : IrredConj) (h3 : SqIntConj) (h4 : KTypeConj) (h5 : KTypeConjInv)
    (h6 : LowKRev) (h7 : VNormRev) : DSConj := by
  intro n ε H _ _ σ lam ⟨hc, hn, hu, hi, hs, ⟨S, hS⟩, hmin⟩
  refine ⟨inferInstanceAs (CompleteSpace H), inferInstanceAs (Nontrivial H), h1 n ε H σ hu, h2 n ε H σ hi, h3 n ε H σ hs,
    ⟨cjSub S, by rw [h6]; exact h4 n ε H σ _ S hS⟩, fun μ S' hS' => ?_⟩
  have := hmin (revP μ) (cjSubInv S') (h5 n ε H σ μ S' hS')
  rw [h6, h7]
  calc vNormSq ε (lowK ε lam) ≤ vNormSq ε (revP μ) := this
    _ = vNormSq (revE ε) (revP (revP μ)) := (h7 n ε (revP μ)).symm
    _ = vNormSq (revE ε) μ := by rw [dualWeight_dualWeight]

end PI.ZuckTensorWork
end
