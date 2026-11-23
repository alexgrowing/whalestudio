import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def RhoUni : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (p : B.SS k r), D.inSS p → ∃ p' : B.SS k r, D.inSS p' ∧
      ∀ X Y : B.Mat k r → (Wq →L[ℂ] Wp),
        ∫ x : Mt k r, B.hsInner (B.rho D p X (Matrix.of x)) (Y (Matrix.of x)) ∂D.μG =
          ∫ x : Mt k r, B.hsInner (X (Matrix.of x)) (B.rho D p' Y (Matrix.of x)) ∂D.μG

def FormAdj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ F F' : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F → B.SuppIn (B.GPos D) F →
      B.CkOn ⊤ (B.GV k r) F' → HasCompactSupport F' → B.SuppIn (B.GPos D) F' →
      ∫ x : Mt k r, B.hsInner (B.opApply Θ F (Matrix.of x)) (F' (Matrix.of x)) ∂D.μG =
        ∫ x : Mt k r, B.hsInner (F (Matrix.of x)) (B.opAdj Θ F' (Matrix.of x)) ∂D.μG

def AdjIntAsm : Prop := RhoUni → FormAdj → AdjInt

theorem adjInt_of_parts (hA : AdjIntAsm) (hU : RhoUni) (hF : FormAdj) : AdjInt := hA hU hF

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
