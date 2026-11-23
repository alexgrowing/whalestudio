import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PTopDensFr

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def fdMaj (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (A : ℝ) (g : B.Mat k r) : ENNReal :=
  ∫⁻ x : B.SS k r, ENNReal.ofReal (B.gN (B.sgs x g) ^ (-A)) ∂((D.μW.prod μ0).prod (D.μW'.prod μ0'))

def FdLocal (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) : Prop :=
  ∀ g₀ ∈ B.GV k r, 0 < Gf k r D.z D.z' g₀ → ∃ (O : Set (B.Mat k r)) (Λ₁ : B.Mat k r → (Wp →L[ℂ] Wp))
    (Λ₂ : B.Mat k r → (Wq →L[ℂ] Wq)), IsOpen O ∧ g₀ ∈ O ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ₁ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ₂ O ∧
    ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r D.z D.z' g → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp),
      frVal D μ0 μ0' F L g = (Λ₁ g).comp ((fibInt D μ0 μ0' F g).comp (Λ₂ g))

end

def FdGram : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), 1 ≤ r → B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∃ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L ∧ FdLocal D μ0 μ0' L

def FdLifts : Prop :=
  FibreBound → ∃ Cl : ℕ, ∀ C₂ : ℕ, ∃ CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∀ μ0 μ0' : Measure (Mt k r), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L → FdLocal D μ0 μ0' L →
    ∃ K : ℝ, ContDiff ℝ (C₂ * (m' + 2) ^ 2) (phi0 D μ0 μ0' L F' hps) ∧
      ∀ i ≤ C₂ * (m' + 2) ^ 2, ∀ Z : G.Mat (p + (m' + 1 + 1)),
        ((∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → castM hps.symm (Zhat k r D.z D.z' g) ≠ Z) →
          iteratedFDeriv ℝ i (phi0 D μ0 μ0' L F' hps) Z = 0) ∧
        ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → castM hps.symm (Zhat k r D.z D.z' g) = Z →
          ENNReal.ofReal ‖iteratedFDeriv ℝ i (phi0 D μ0 μ0' L F' hps) Z‖ ≤
            ENNReal.ofReal K * fdMaj D μ0 μ0' (A - (Cl : ℝ) * r * i) g

def FdDecayOf : Prop :=
  FibreBound → FdLifts → ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∀ μ0 μ0' : Measure (Mt k r), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L → FdLocal D μ0 μ0' L →
    ∃ K : ℝ, U.DecayAll (C₂ * (m' + 2) ^ 2)
        (fun j => A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) K
        (phi0 D μ0 μ0' L F' hps)

end PI.UnitaryGroupMassFormula.DLm
