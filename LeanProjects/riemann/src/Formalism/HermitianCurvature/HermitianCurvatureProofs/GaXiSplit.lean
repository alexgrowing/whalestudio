import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroPointOver
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def rcAct {k p ρ : ℕ} (y : B.Mat k ρ) (x : U.RC k p ρ) : U.RC k p ρ := (fun v a => (y * Matrix.of x.1) v a, x.2)

def lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  U.wP σ * U.lowW σ v * (U.wP σ)⁻¹

def MMapEmbG : Prop := ∀ (k p ρ : ℕ) (Z : Matrix (Fin p) (Fin p) ℂ) (γ y₁ y₂ : B.Mat k ρ),
  U.mMap k p ρ Z (y₁ * γ * y₂) = U.embG k p ρ y₁ * U.mMap k p ρ Z γ * U.embG k p ρ y₂

def MMapLZU : Prop := ∀ (k p ρ : ℕ) (l Z u : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ), IsUnit l.det →
  U.mMap k p ρ (l * Z * u) γ = U.muP k p ρ (lᴴ)⁻¹ * U.mMap k p ρ Z γ * U.muP k p ρ u

def EmbGMuP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (q : Matrix (Fin p) (Fin p) ℂ),
  U.embG k p ρ y * U.muP k p ρ q = U.muP k p ρ q * U.embG k p ρ y

def EmbGRn : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (x : U.RC k p ρ), yᴴ * Hpk k ρ * y = Hpk k ρ →
  U.embG k p ρ y * U.Rn k p ρ x = U.Rn k p ρ (rcAct y x) * U.embG k p ρ y

def HeadHEq : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (v : U.LW σ → ℂ) (u : G.UT p → ℂ),
  U.headH σ d v u = lhOf σ v * U.hMat σ d * G.upper u ∧ G.IsLowerUni (lhOf σ v)

def ZjHZero : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : U.XiH p 0 σ) (Z : G.Mat 0),
  U.ZjH σ d η Z = U.headH σ d η.2.1 η.2.2

def GaXiSplit : Prop := ∀ (k p ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0)
  (h ν h' ν' g : B.Mat k ρ), IsUnit h.det → IsUnit ν.det → h'ᴴ * Hpk k ρ * h' = Hpk k ρ →
  U.gaXi k ρ σ d ξ Z (h⁻¹ * ν⁻¹ * g * ν' * h') =
    (U.Rn k p ρ (-ξ.1.1) * U.muP k p ρ (lhOf σ ξ.2.2.1)ᴴ⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)) *
      U.mMap k p ρ (U.hMat σ d) g *
      (U.embG k p ρ ν' * U.muP k p ρ (G.upper ξ.2.2.2) * U.Rn k p ρ (rcAct h' ξ.1.2)) * U.embG k p ρ h'

def LeftMem : Prop := ∀ (k p ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.RC k p ρ) (l : Matrix (Fin p) (Fin p) ℂ)
  (h ν : B.Mat k ρ), inWb k ρ z → G.IsLowerUni l → h ∈ UWset k ρ z → ν ∈ Nset k ρ →
  U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹) ∈ Sset k (p + ρ) (liftVec k p ρ z)

def PsiRight : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (ν' : B.Mat k ρ) (u : G.UT p → ℂ)
  (x : U.RC k p ρ), inWb k ρ z' → ν' ∈ Nset k ρ →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.embG k p ρ ν' * U.muP k p ρ (G.upper u) * U.Rn k p ρ x) =
    psi k ρ z' cStd ν' * psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u)) *
      psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiRnAct : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (h' : B.Mat k ρ) (x : U.RC k p ρ),
  inWb k ρ z' → h' ∈ UWset k ρ z' →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ (rcAct h' x)) = psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiMuP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (u : G.UT p → ℂ), inWb k ρ z' →
  star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u))) = G.psi U.betaU (U.supS (G.upper u))

def MuNLeft : Prop := ∀ (k p ρ : ℕ),
  D.muN k (p + ρ) = ((U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ))).map
    (fun x => Matrix.of.symm (U.embG k p ρ (Matrix.of x.2.2) * U.muP k p ρ (G.upper x.2.1) * U.Rn k p ρ x.1))

def RcActMP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ), ‖y.det‖ = 1 →
  MeasurePreserving (rcAct (p := p) y) (U.muRC k p ρ) (U.muRC k p ρ)

def RightMP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (μj : Measure (Mt k ρ)) (μ0' : Measure (Mt k (p + ρ))),
  B.IsHaarOn (UWset k ρ z') μj → μj Set.univ = 1 → μ0' = μj.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
  MeasurePreserving
    (fun y : (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (G.UT p → ℂ)) =>
      (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl y.1.1,
        Matrix.of.symm (U.embG k p ρ (Matrix.of y.1.2) * U.muP k p ρ (G.upper y.2.2) *
          U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1))))
    ((μj.prod (D.muN k ρ)).prod ((U.muRC k p ρ).prod volume)) (μ0'.prod (D.muN k (p + ρ)))

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
