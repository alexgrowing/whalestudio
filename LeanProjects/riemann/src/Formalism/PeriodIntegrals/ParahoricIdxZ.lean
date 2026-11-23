import Mathlib
import Formalism.DoubleCosetMeasures.StatementV
noncomputable section

open MeasureTheory Matrix ComplexConjugate Finset

namespace PI.ParahoricIdxZ

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def blockCond {F : Type} [Field F] (O : Subring F) (ϖ : F) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (A : GL (Fin (a + t)) F) : Prop :=
  let M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A : Matrix (Fin (a + t)) (Fin (a + t)) F)
  (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = M.toBlocks₁₁) ∧
  (∀ i j, M.toBlocks₁₂ i j ∈ O) ∧
  M.toBlocks₂₁ ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ∧
  (∃ D ∈ Formalism.DoubleCosetMeasures.GLint O t, (D : Matrix (Fin t) (Fin t) F) = M.toBlocks₂₂)

end PI.ParahoricIdxZ

namespace PI

open PI.ParahoricIdxZ in

def ParahoricIdxZ : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (O : Subring F),
    IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a → IsCompact (J' : Set (GL (Fin a) F)) →
    ∀ (ρ : J' →* ℂˣ), (∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) →
    ∀ (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (lam : J' →* ℂˣ),
    (∀ k : J', ((χ (Matrix.GeneralLinearGroup.det (k : GL (Fin a) F)) : ℂˣ) : ℂ) *
        (((nrm ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) F) : Fˣ) : F)) ^
          (((a + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((ρ k : ℂˣ) : ℂ) * conj ((lam k : ℂˣ) : ℂ) = 1) →
    ∀ (c : GL (Fin a) F → ℂ), (∀ g : GL (Fin a) F, ∀ k : J', c (g * k) = ((lam k : ℂˣ) : ℂ) * c g) →
    c 1 = 1 →
    ∀ (μ : Measure (GL (Fin a) F)) [μ.IsMulLeftInvariant], μ (J' : Set (GL (Fin a) F)) = 1 →
    ∀ (ν₁ : Measure (Matrix (Fin a) (Fin a) F)) [ν₁.IsAddLeftInvariant] [SFinite ν₁],
    ν₁ (Formalism.DoubleCosetMeasures.intMat O a a) = 1 →
    ∀ (ν₂ : Measure (Matrix (Fin t) (Fin a) F)) [ν₂.IsAddLeftInvariant] [SFinite ν₂],
    ν₂ (Formalism.DoubleCosetMeasures.intMat O t a) = 1 →
    ∀ (J : Subgroup (GL (Fin (a + t)) F)), (∀ A, A ∈ J ↔ blockCond O ϖ J' A) →
    let q : ℝ := Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)
    ((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index : ℂ) * ((zetaProd q (a + t) : ℝ) : ℂ) *
        Formalism.DoubleCosetMeasures.localZ μ ((ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2)) χ nrm
          (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) c =
      ((zetaProd q t : ℝ) : ℂ)

end PI
