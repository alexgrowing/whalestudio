import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Wave

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def wvG (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => fsv s (Dmin k r z z' g ⟨1, by omega⟩) • F g

variable [FiniteDimensional ℂ Wq]

def NiceAll (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ JC.NiceCoef D ε F

end Wave

def RDWave : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (hr : 0 < r) (ε : ℝ) (s : ℂ) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
    (JC.NiceCoef D ε G → JC.NiceCoef D ε (wvG D.z D.z' s G)) ∧
    ∀ y ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.JF D (wvG D.z D.z' s G)) y.1 y.2 =
      fsv s (y.1 ⟨0, hr⟩) • resG k r (Fin.last r) (B.JF D G) y.1 y.2

def RDBeta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ : Measure (Mt k r)), B.IsHaarOn (Glev k r (Fin.last r)) μ →
    ∃ C1 : ℂ, C1 ≠ 0 ∧ ∀ (F H : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Ψ : RadSp k r D.z D.z' D.π D.π'),
      (∀ (A : ℝ) (m : ℕ), B.InCC A m F) → (∀ (A : ℝ) (m : ℕ), B.InCC A m H) →
      (∀ y ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ DomR k r D.z D.z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D H) y.1 y.2) →
      ∀ c : Fin r → ℂ, LocFacts₂ μ 0 Φ Ψ c = C1 * B.beta D F H

def RDBdd : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F H : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ (A : ℝ) (m : ℕ), B.InCC A m F) → (∀ (A : ℝ) (m : ℕ), B.InCC A m H) →
    ∃ K : ℝ, ∀ s : ℂ, ‖B.beta D (wvG D.z D.z' s F) H‖ ≤ K

def RDHyp (Q : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], B.RealPlaceData k r Wp Wq → Prop) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    Q P.k P.r Wp Wq D

def RDIdent : Prop :=
  RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∃ Θ : Fin 4 → (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp),
      (∀ j F, NiceAll D F → NiceAll D (Θ j F)) ∧
      ∀ (s : ℂ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' →
        s * B.beta D (wvG D.z D.z' s F) F' =
          B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F') - B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')

section Second

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def RDOpsProp (D : B.RealPlaceData k r Wp Wq) (Θ : Fin 4 → B.DiffOp k r Wp Wq) : Prop :=
  ∀ j, B.SmoothCoef (B.GPos D) (Θ j) ∧ B.Commutes D (B.GPos D) (Θ j) ∧
    (∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 ≤ d ∧ B.PolyCoef D ε d (B.opOrder (Θ j) + 5) (Θ j)) ∧
    ∀ F, NiceAll D F → NiceAll D (B.opApply (Θ j) F) ∧ NiceAll D (B.opAdj (Θ j) F)

def RDRadIdProp (D : B.RealPlaceData k r Wp Wq) (Θ : Fin 4 → B.DiffOp k r Wp Wq) : Prop :=
  ∀ (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → ∀ q ∈ B.Qset D,
    s • B.JF D (wvG D.z D.z' s F) (B.gq D q) =
      B.JF D (B.opAdj (Θ 0) (wvG D.z D.z' s (B.opApply (Θ 1) F))) (B.gq D q) -
        B.JF D (B.opAdj (Θ 2) (wvG D.z D.z' s (B.opApply (Θ 3) F))) (B.gq D q)

end Second

def RDIdentAB : Prop :=
  RDHyp fun k r Wp Wq _ _ _ _ _ _ D => ∃ Θ : Fin 4 → B.DiffOp k r Wp Wq, RDOpsProp D Θ ∧ RDRadIdProp D Θ

def RDIdentOfAB : Prop := RDIdentAB → RDIdent

end Formalism.FourierDecayAlt.P.CutSE
