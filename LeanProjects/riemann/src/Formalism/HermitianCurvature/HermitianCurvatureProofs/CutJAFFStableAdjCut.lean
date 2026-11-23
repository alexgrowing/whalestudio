import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def FundG : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A A' : B.Mat k r → (Wq →L[ℂ] Wp)), ContinuousOn A (B.GV k r) → ContinuousOn A' (B.GV k r) →
    (∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ → B.SuppIn (B.GPos D) φ →
      ∫ x : Mt k r, B.hsInner (A (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
        ∫ x : Mt k r, B.hsInner (A' (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG) →
    ∀ g ∈ B.GPos D, A g = A' g

def AdjCont : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ContinuousOn (B.opAdj Θ (B.rho D p f)) (B.GV k r) ∧
        ContinuousOn (B.rho D p (B.opAdj Θ f)) (B.GV k r)

def AdjInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ →
        B.SuppIn (B.GPos D) φ →
        ∫ x : Mt k r, B.hsInner (B.opAdj Θ (B.rho D p f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
          ∫ x : Mt k r, B.hsInner (B.rho D p (B.opAdj Θ f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG

theorem adjComm_of_parts (hF : FundG) (hC : AdjCont) (hI : AdjInt) : AdjComm := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp g hg
  obtain ⟨c1, c2⟩ := hC k r Wp Wq D Θ hs f hf hfc hfs p hp
  exact hF k r Wp Wq D _ _ c1 c2 (fun φ h1 h2 h3 => hI k r Wp Wq D Θ hs hc f hf hfc hfs p hp φ h1 h2 h3) g hg

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
