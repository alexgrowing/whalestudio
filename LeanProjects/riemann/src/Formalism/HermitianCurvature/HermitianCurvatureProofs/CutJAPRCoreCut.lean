import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

section defs

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rc (Z : Q.Mx k r) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g

def wordR (w : List (Q.Mx k r)) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  w.foldr (fun Z h => Rc Z h) f

def dZV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 - Complex.I • fderiv ℝ f ζ Complex.I)

def dZbV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 + Complex.I • fderiv ℝ f ζ Complex.I)

end defs

def GLc (k r : ℕ) (Z : Q.Mx k r) : Prop :=
  Q.inLieLev k r (Fin.last r) (hpart1 (Hpk k r) Z) ∧ Q.inLieLev k r (Fin.last r) (hpart2 (Hpk k r) Z)

def GWc (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Z : Q.Mx k r) : Prop :=
  P.QrD.InLieW k r z (hpart1 (Hpk k r) Z) ∧ P.QrD.InLieW k r z (hpart2 (Hpk k r) Z)

def Dp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) := {g | 0 < Q.GGl k r z z' g}

def mu0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r := NF.muZ k r (TheSec.theSection k r z z') ζ

def etaZ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ

def etaZb (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ

def RcLin : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
    ∀ (a : ℂ) (Z Z' : Q.Mx k r), GLc k r Z → GLc k r Z' → Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g

def RcSmooth : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f f' : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → Q.SmoothLev k r (Fin.last r) D f' → ∀ Z : Q.Mx k r, GLc k r Z →
      Q.SmoothLev k r (Fin.last r) D (Rc Z f) ∧
      (∀ (a : ℂ), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, Rc Z (fun x => a • f x + f' x) g = a • Rc Z f g + Rc Z f' g) ∧
      ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E'), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
        Rc Z (fun x => L (f x)) g = L (Rc Z f g)

def RcComm : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ Z₁ Z₂ : Q.Mx k r, GLc k r Z₁ → GLc k r Z₂ →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
      Rc Z₁ (Rc Z₂ f) g - Rc Z₂ (Rc Z₁ f) g = Rc (Z₁ * Z₂ - Z₂ * Z₁) f g

def LeftCov : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)), IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) → inWb k r z →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z, ∀ g ∈ D, h * g ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g)) →
    ∀ μ ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ B : Q.Mx k r, GWc k r z B →
      GLc k r (μ⁻¹ * B * μ) ∧ Rc (μ⁻¹ * B * μ) F μ = (P.QrD.ecOp π B).comp (F μ)

def RightCov : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)), IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') → inWb k r z' →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z', ∀ g ∈ D, g * h ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h)) →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ A : Q.Mx k r, GWc k r z' A →
      GLc k r A ∧ Rc A F g = (F g).comp (P.QrD.ecOp π' A)

def SecDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
      GLc k r (etaZ k r z z' ζ) ∧ GLc k r (etaZb k r z z' ζ) ∧ (mu0 k r z z' ζ) ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F →
        Rc (etaZ k r z z' ζ) F (mu0 k r z z' ζ) = dZV (fun w => F (mu0 k r z z' w)) ζ ∧
        Rc (etaZb k r z z' ζ) F (mu0 k r z z' ζ) = dZbV (fun w => F (mu0 k r z z' w)) ζ

def Decomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ a b : Fin (k + 1), ∃ (n₁ n₂ : ℕ) (B₁ : Fin n₁ → Q.Mx k r) (b₁ : Fin n₁ → ℂ → ℂ) (B₂ : Fin n₂ → Q.Mx k r)
      (b₂ : Fin n₂ → ℂ → ℂ) (β₁ β₂ : ℂ → ℂ),
      (∀ t, GWc k r z' (B₁ t)) ∧ (∀ t, GWc k r z (B₂ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₁ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₂ t)) ∧
      PS (Tz k r z * Tz k r z') β₁ ∧ PS (Tz k r z * Tz k r z') β₂ ∧
      ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
        Matrix.single (wI k r a) (wI k r b) (1 : ℂ) =
          ∑ t, b₁ t ζ • B₁ t + (mu0 k r z z' ζ)⁻¹ * (∑ t, b₂ t ζ • B₂ t) * (mu0 k r z z' ζ) +
            β₁ ζ • etaZ k r z z' ζ + β₂ ζ • etaZb k r z z' ζ

def PSCalc : Prop :=
  ∀ (TT : ℝ), 0 < TT →
    (∀ c : ℂ, PS TT (fun _ => c)) ∧ PS TT id ∧ PS TT (fun ζ => conj ζ) ∧ PS TT (sig TT) ∧ PS TT (fun ζ => (gg TT ζ)⁻¹) ∧
    (∀ f g, PS TT f → PS TT g → PS TT (fun ζ => f ζ + g ζ) ∧ PS TT (fun ζ => f ζ * g ζ)) ∧
    (∀ f, PS TT f → PS TT (NF.dZ f) ∧ PS TT (NF.dZb f)) ∧
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V'],
      (∀ f g : ℂ → V, PSV TT f → PSV TT g → PSV TT (fun ζ => f ζ + g ζ)) ∧
      (∀ (a : ℂ → ℂ) (f : ℂ → V), PS TT a → PSV TT f → PSV TT (fun ζ => a ζ • f ζ)) ∧
      (∀ (L : V →ₗ[ℂ] V') (f : ℂ → V), PSV TT f → PSV TT (fun ζ => L (f ζ))) ∧
      (∀ (f : ℂ → V), PSV TT f → PSV TT (dZV f) ∧ PSV TT (dZbV f)) ∧
      (∀ v : V, PSV TT (fun _ => v))

def LowerUnipotentMatrixWords : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ Y : ℂ, ∃ (n : ℕ) (κ : Fin n → ℂ → ℂ) (w : Fin n → List (Q.Mx k r)),
      (∀ i, PS (Tz k r z * Tz k r z') (κ i)) ∧ (∀ i, ∀ Z ∈ w i, ∃ a b : Fin (k + 1), Z = Matrix.single (wI k r a) (wI k r b) 1) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F → ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
          Q.tL k r z z' (Fin.last r) Y 1 0 F (mu0 k r z z' ζ) = ∑ i, κ i ζ • wordR (w i) F (mu0 k r z z' ζ)

def WordPSV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (X₀ : Wq →L[ℂ] Wp),
      (∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = X₀) →
      ∀ c ∈ OmX P.r, ∀ w : List (Q.Mx P.k P.r), (∀ Z ∈ w, GLc P.k P.r Z) →
        PSV P.TT (fun ζ => wordR w ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))

def WordPSVOfCut : Prop :=
  RcLin → RcSmooth → RcComm → LeftCov → RightCov → SecDeriv → Decomp → PSCalc → WordPSV

def CorePolyOfCut : Prop := LowerUnipotentMatrixWords → WordPSV → PSCalc → CorePoly

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
