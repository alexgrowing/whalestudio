import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def PolyLift (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (a : RA P Bs) : Prop :=
  ∃ Θ : B.DiffOp P.k P.r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp o κ Θ ∧ TL.RadIs P Bs Θ a.1

end actual

def BasicLiftAll (a : ℕ → ℕ) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)),
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ x ∈ basics d,
      x ∈ nfSpan d {θ | PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) θ} 0 (a P.r) 1

def CutPow (e : ℕ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → φ x = 0) ∧
    ∃ a R : ℝ, ∀ x, R ≤ x → φ x = a * x ^ e

def mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • f g

def WordBound {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (a : ℕ)
    (w : List C.Letter) (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq))
    (K : (ℝ → ℝ) → (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → Prop) : Prop :=
  0 ≤ C ∧ (∀ Θ ∈ Θs, Formalism.FourierDecayAlt.P.CutMP.PolyOp (w.length * (2 * P.r + P.k + 1))
      (w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1))) Θ) ∧
    ∀ φ f, K φ f → ∀ (e : Ix (Fin w.length)) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) →
      0 < TBB.Gp p (TBB.bigPt P.r c) →
      ‖B.hsVec (p.V (p.Θ.Θ w e (mulG p.T.base φ f)) (TBB.bigPt P.r c))‖ ≤
        C * (‖∏ l, c l‖⁻¹ ^ w.length * (TBB.Gp p (TBB.bigPt P.r c))⁻¹ ^ (a * w.length)) *
          (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (TBB.Gp p (TBB.bigPt P.r c))|) *
          (Θs.map fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) (TBB.bigPt P.r c))‖).sum

end

end GlobalTheory.HatNF
