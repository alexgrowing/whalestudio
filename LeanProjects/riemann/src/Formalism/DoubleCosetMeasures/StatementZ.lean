import Formalism.DoubleCosetMeasures.Statement

noncomputable section

open MeasureTheory Matrix ComplexConjugate

namespace Formalism.DoubleCosetMeasures

instance instMeasMat {m n F : Type} [MeasurableSpace F] : MeasurableSpace (Matrix m n F) :=
  inferInstanceAs (MeasurableSpace (m → n → F))

section Weil

variable {F : Type} [Field F] {a : ℕ} {m : Type} [Fintype m]

def omegaS (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (g : GL (Fin a) F)
    (Φ : Matrix m (Fin a) F → ℂ) : Matrix m (Fin a) F → ℂ :=
  fun x => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^ ((Fintype.card m : ℝ) / 2) : ℝ) : ℂ) *
    Φ (x * (g : Matrix (Fin a) (Fin a) F))

variable [MeasurableSpace F]

def weilIP (ν : Measure (Matrix m (Fin a) F)) (Φ₁ Φ₂ : Matrix m (Fin a) F → ℂ) : ℂ :=
  ∫ x, Φ₁ x * conj (Φ₂ x) ∂ν

variable [TopologicalSpace F] [IsTopologicalRing F]

def localZ (μ : Measure (GL (Fin a) F)) (ν : Measure (Matrix m (Fin a) F)) (χ : Fˣ →* ℂˣ)
    (nrm : AbsoluteValue F ℝ) (Φ₁ Φ₂ : Matrix m (Fin a) F → ℂ) (c : GL (Fin a) F → ℂ) : ℂ :=
  ∫ g, weilIP ν (omegaS χ nrm g Φ₁) Φ₂ * conj (c g) ∂μ

end Weil

section DatumU

variable {F : Type} [Field F] {a t : ℕ}

def IIset (O : Subring F) (ϖ : F) : Set (Matrix (Fin t) (Fin a) F) :=
  {y | ∀ i j, ∃ o ∈ O, y i j = ϖ * o}

def Jset (J' : Subgroup (GL (Fin a) F)) : Set (Matrix (Fin a) (Fin a) F) :=
  (fun k : GL (Fin a) F => (k : Matrix (Fin a) (Fin a) F)) '' (J' : Set (GL (Fin a) F))

open Classical in

def phiU (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F)) (ρ : J' →* ℂˣ) :
    Matrix (Fin a ⊕ Fin t) (Fin a) F → ℂ :=
  fun x => if h : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = Matrix.toRows₁ x) ∧
      Matrix.toRows₂ x ∈ IIset O ϖ then ((ρ (Classical.choose h.1) : ℂˣ) : ℂ) else 0

end DatumU

def SuppJ : Prop :=
  ∀ (F : Type) [Field F] [MeasurableSpace F] (a t : ℕ) (O : Subring F) (ϖ : F)
    (J' : Subgroup (GL (Fin a) F)) (ρ : J' →* ℂˣ) (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ)
    (ν : Measure (Matrix (Fin a ⊕ Fin t) (Fin a) F)) (g : GL (Fin a) F), g ∉ J' →
    weilIP ν (omegaS χ nrm g (phiU (t := t) O ϖ J' ρ)) (phiU O ϖ J' ρ) = 0

def LemmaUSplit : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (a t : ℕ) (O : Subring F),
    IsOpen (O : Set F) → ∀ (ϖ : F), ϖ ≠ 0 → ∀ (J' : Subgroup (GL (Fin a) F)),
    IsCompact (J' : Set (GL (Fin a) F)) →
    (∀ k ∈ J', IsInt O ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)) →
    ∀ (ρ : J' →* ℂˣ), (∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) →
    ∀ (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (lam : J' →* ℂˣ),
    (∀ k : J', ((χ (Matrix.GeneralLinearGroup.det (k : GL (Fin a) F)) : ℂˣ) : ℂ) *
        (((nrm ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) F) : Fˣ) : F)) ^
          (((a + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((ρ k : ℂˣ) : ℂ) * conj ((lam k : ℂˣ) : ℂ) = 1) →
    ∀ (c : GL (Fin a) F → ℂ), (∀ g : GL (Fin a) F, ∀ k : J', c (g * k) = ((lam k : ℂˣ) : ℂ) * c g) →
    ∀ (μ : Measure (GL (Fin a) F)) (ν₁ : Measure (Matrix (Fin a) (Fin a) F))
      (ν₂ : Measure (Matrix (Fin t) (Fin a) F)) [SFinite ν₁] [SFinite ν₂],
    localZ μ ((ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2)) χ nrm
        (phiU O ϖ J' ρ) (phiU O ϖ J' ρ) c =
      (((μ (J' : Set (GL (Fin a) F))).toReal * (ν₁ (Jset J')).toReal *
        (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) * conj (c 1)

end Formalism.DoubleCosetMeasures
