import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ContraPair

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in

def barK (k : Kinf E a) : Kinf E a :=
  ⟨(star k.1)ᵀ, Matrix.mem_unitaryGroup_iff.2 (by
    have h : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
    have e : star ((star k.1)ᵀ) = k.1ᵀ := by
      ext i j : 1
      simp [Matrix.star_apply]
    have h' : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
    rw [e, ← Matrix.transpose_mul, h', Matrix.transpose_one])⟩

omit [IsTotallyComplex E] in

def invTOp : Op E a → Op E a
  | .fin k => .fin (invT a (Af E) k)
  | .cpt k => .cpt (barK k)
  | .lie X => .lie (toL (-(Matrix.of X)ᵀ))

def Paired (π π' : CuspSub E a) (s : Op E a → Op E a) : Prop :=
  ∃ B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ k φ ψ, B (π.op (.fin k) φ) (π'.op (s (.fin k)) ψ) = B φ ψ) ∧
    (∀ k φ ψ, B (π.op (.cpt k) φ) (π'.op (s (.cpt k)) ψ) = B φ ψ) ∧
    ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π'.op (s (.lie X)) ψ) = 0

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

def conjOp : Op L a → Op L a
  | .fin k => .fin (GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k)
  | .cpt k => .cpt (barK k)
  | .lie X => .lie fun i j => star (X i j)

def DualIsConj (π : CuspSub L a) : Prop := Paired π π conjOp

def DualIsConjBy (π : CuspSub L a) (ψ : HChar L) : Prop := Paired (π.twist ψ⁻¹) π conjOp

theorem dualIsConjBy_one (π : CuspSub L a) : DualIsConjBy π 1 ↔ DualIsConj π := by
  rw [DualIsConjBy, inv_one, CuspSub.twist_one, DualIsConj]

structure PolarizedPair (π : CuspSub L a) (χ : HChar (maximalRealSubfield L)) : Prop where
  sign : ∀ v : InfinitePlace (maximalRealSubfield L), χ.locInf v (-1) = (-1) ^ a
  dual : DualIsConjBy π (GlobalTheory.GalOfCusp.compNorm L χ)

end GlobalTheory.ContraPair

end
