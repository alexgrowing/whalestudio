import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PDownTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def IsUT {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) : Prop := (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1

def castM {n n' : ℕ} (h : n = n') (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n') (Fin n') ℂ :=
  Matrix.reindex (finCongr h) (finCongr h) M

def topPt {p s r : ℕ} (h : p + s = r + 1) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (Z : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  castM h (U.blk2 (U.hMat σ d) 0 0 Z)

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def ZOrb (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Prop :=
  ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUT u ∧ IsUT u' ∧ Zhat k r D.z D.z' g = u.conjTranspose * M * u'

end

def TopNF : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (γ : B.Mat k r) (i : ℕ),
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → HasRun D γ i (r + 1) →
    ∃ (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (z₀ : ℂ),
      p + 1 = i ∧ (∀ a, d a ≠ 0) ∧ z₀ ≠ 0 ∧ ZOrb D γ (topPt hps σ d (z₀ • G.wMat (m' + 1 + 1)))

def TopLower : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (γ : B.Mat k r) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (z₀ : ℂ) (m : ℕ),
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → (∀ a, d a ≠ 0) → z₀ ≠ 0 →
    ZOrb D γ (topPt hps σ d (z₀ • G.wMat (m' + 1 + 1))) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ → c * t ^ (m' + 1) = (-1) ^ (m' + 3) * z₀ ^ (m' + 2) →
      ∃ (g : B.Mat k r) (μR : Measure (Mt k r)), B.IsHaarOn (Rset g) μR ∧ IsRelevant D g ∧
        0 < Gf k r D.z D.z' g ∧ zc D g ≤ m ∧ ZOrb D g (topPt hps σ d (G.ptBlock (m' + 1) t c))

def TopSlice : Prop :=
  ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) → (∀ a, d a ≠ 0) →
    ∃ (β : ℂ) (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) (e : ℕ → ℝ) (K : ℝ),
      β ≠ 0 ∧ U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        (A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) / (5 * ((r : ℝ) + 1))
          - (C : ℝ) * (r : ℝ) ^ 2 ≤ e j / (5 * ((r : ℝ) + 1))) ∧
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (G.ptBlock (m' + 1) t c)) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c = 0 ↔ orbI D g θ F' = 0)) ∧
      (∀ z : ℂ, z ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (z • G.wMat (m' + 1 + 1))) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z = 0 ↔ orbI D g θ F' = 0))

end PI.UnitaryGroupMassFormula.DLm
