import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.Development

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def HasRun (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (i j : ℕ) : Prop :=
  1 ≤ i ∧ i < j ∧ j ≤ r + 1 ∧
    (∀ l : Fin (r + 2), l.val + 1 = i → Dmin k r D.z D.z' γ l ≠ 0) ∧
    (∀ l : Fin (r + 2), i ≤ l.val → l.val < j → Dmin k r D.z D.z' γ l = 0) ∧
    (∀ l : Fin (r + 2), l.val = j → Dmin k r D.z D.z' γ l ≠ 0)

def Hyps (CV : ℕ) (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  1 ≤ r ∧ 0 < ε ∧ (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A ∧ mmV CV r ≤ mm ∧ B.InCC A mm F' ∧
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) ∧ (∀ g ∈ bigPos D, B.JF D F' g = 0)

end

def RunExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r),
    0 < Gf k r D.z D.z' γ → 1 ≤ zc D γ → ∃ i j : ℕ, HasRun D γ i j

def DownJ (CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i j : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i j → j ≤ r → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0

def DownTop (CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i (r + 1) → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0

def AdmExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)),
    B.IsHaarOn (Rset γ) μR → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → ∃ θ : B.SS k r → ℝ, admitted D γ μR θ

def AdmConv (CV : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR →
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS

def BigTheta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ = 0 → admitted D γ μR θ →
    ∃ c : ℝ, 0 < c ∧ ∀ p, D.inSS p → θ p = c

def BigOf (CV : ℕ) : Prop := BigTheta → B.JtauOne → StepBig CV

theorem stepDown_of (CV : ℕ) (hR : RunExists) (hJ : DownJ CV) (hT : DownTop CV) (hA : StepAdm CV) :
    StepDown CV := by
  intro m ih k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ μR θ hH hr hε hA' hmm hF hs hJ0 hrel hG hz hθ hi
  by_cases h0 : zc D γ = 0
  · exact ih k r Wp Wq D A ε mm F' γ μR θ hH hr hε hA' hmm hF hs hJ0 hrel hG (by omega) hθ hi
  · obtain ⟨i, j, hij⟩ := hR k r Wp Wq D γ hG (by omega)
    have hy : Hyps CV D A ε mm F' := ⟨hr, hε, hA', hmm, hF, hs, hJ0⟩
    rcases Nat.lt_or_ge j (r + 1) with hj | hj
    · exact hJ hA m ih k r Wp Wq D A ε mm F' γ μR θ i j hH hy hrel hG hz hij (by omega) hθ hi
    · have hjr : j = r + 1 := le_antisymm hij.2.2.1 hj
      subst hjr
      exact hT hA m ih k r Wp Wq D A ε mm F' γ μR θ i hH hy hrel hG hz hij hθ hi

end PI.UnitaryGroupMassFormula.DLm
