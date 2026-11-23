import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

def CoefG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)

def OpCCg : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (d Bg A η : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    0 < η → 0 ≤ Bg → B.SmoothCoef (B.GPos Bs) Θ → CoefG Bs Θ d Bg →
    B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC (A - Bg * m) m F) →
    (∀ g ∈ B.GV k r, Gf k r Bs.z Bs.z' g < η → F g = 0) →
    (B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opApply Θ F)) ∧
    (B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opAdj Θ F))

def AgreeOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ℝ),
    J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} →
    (∀ q ∈ JF.QDom k r Bs.z Bs.z', Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', Gf k r Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g

def ThetaJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (UU : Set (B.Mat k r)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    UU ⊆ JF.Om k r Bs.z Bs.z' → B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF Bs F) →
    (∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g) ∧
      ∀ g ∈ UU, B.opAdj Θ (B.JF Bs F) g = B.JF Bs (B.opAdj Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

def ThetaJApply : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
