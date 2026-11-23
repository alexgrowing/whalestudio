import Formalism.PeriodIntegrals.HwConjInf

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut

namespace PI.UnitaryGroupMassFormula.HwConjInf

def HwConjW : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ),
    a.HWAt τ lam → a.HWAt (ComplexEmbedding.conjugate τ) lam' → lam' = fun i => -lam (Fin.rev i)

def HwUniqAt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (τ : L →+* ℂ) (lam mu : Fin n → ℤ),
    a.HWAt τ lam → a.HWAt τ mu → lam = mu

def ConjSwap : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ),
    a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i))

def ratPt {L : Type} [Field L] {n : ℕ} (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* ℂ) × Fin n × Fin n → ℂ :=
  fun p => p.1 (γ₀ p.2.1 p.2.2)

def InV {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (y : (L →+* ℂ) × Fin n × Fin n → ℂ) : Prop :=
  ∀ σ : L →+* ℂ, ∃ B : GL (Fin n) ℂ, ∀ i j,
    y (σ, i, j) = B.val i j ∧ y (ComplexEmbedding.conjugate σ, i, j) = (B⁻¹).val j i

def DensStep : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0) →
    ∀ y, InV y → MvPolynomial.eval y F = 0

def gPt {n : ℕ} (g : GL (Fin n) ℂ) : Bool × Fin n × Fin n → ℂ := fun p =>
  if p.1 then g.val p.2.1 p.2.2 else (g⁻¹).val p.2.2 p.2.1

def GLStep : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (R : GL (Fin n) ℂ → Matrix ι ι ℂ) (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ),
    (∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j)) →
    (∀ g h, R (g * h) = R g * R h) →
    ∀ (S : Set (Matrix ι ι ℂ)), (∀ s ∈ S, ∀ g, s * R g = R g * s) →
    ∀ (v u : ι → ℂ) (lam mu : Fin n → ℤ),
    (∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) v = (∏ i, B.val i i ^ lam i) • v) →
    (∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) u = (∏ i, B.val i i ^ mu i) • u) →
    Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)} = ⊤ →
    Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) u)} = ⊤ →
    v ≠ 0 → u ≠ 0 → lam = mu

def GlueStep : Prop := DensStep → GLStep → HwUniqAt

end PI.UnitaryGroupMassFormula.HwConjInf
