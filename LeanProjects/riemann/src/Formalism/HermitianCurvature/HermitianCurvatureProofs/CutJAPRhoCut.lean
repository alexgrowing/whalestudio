import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRho
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section K

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

def Kset (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Set Wp :=
  {x | ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, b] Fr → ∀ w : ℂ, capRep k r π Fr w x = f w • x}

def K (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Submodule ℂ Wp :=
  Submodule.span ℂ (Kset k r z b π f)

end K

def FrameLoc : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 2 ≤ k → inWb k r z → 0 < Tz k r z →
    ∀ a₀ : Fin (2 * r + k + 1) → ℂ, 0 < PRho.nrmW k r z a₀ →
      ∃ Fr : (Fin (2 * r + k + 1) → ℂ) → Fin (k - 1) → Fin (2 * r + k + 1) → ℂ,
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fr a₀ ∧ ∀ᶠ a in 𝓝 a₀, IsFrameOf k r [z, SSn.prWv k r z a] (Fr a)

def CapSmooth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r m : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), Qr.IsRepW k r z π → ∀ w : ℂ,
    ∃ C : (Fin m → Fin (2 * r + k + 1) → ℂ) → (Wp →L[ℂ] Wp), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C ∧
      ∀ Bs, IsFrameOf k r [z] Bs → ∀ v, C Bs v = capRep k r π Bs w v

def EigOrth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r : ℕ)
    (z e : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Qr.IsRepW k r z π →
    (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) →
    (∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr) →
    ∀ (f g : ℂ → ℂ) (x y : Wp), x ∈ Kset k r z e π f → y ∈ Kset k r z e π g → (∃ w, f w ≠ g w) → inner ℂ x y = 0

def Lagrange : Prop :=
  EigOrth → ∀ (P : M.Par), P.OK → 2 ≤ P.k → ∃ (w : ℂ) (p : M.Ty P → Polynomial ℂ),
    ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      (z e : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)),
      inWb P.k P.r z → 0 < Tz P.k P.r z → IsType P.k P.r z π P.u →
      inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 → herm (Hpk P.k P.r) e e = 1 →
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Fr →
      ∀ C : Wp →L[ℂ] Wp, (∀ v, C v = capRep P.k P.r π Fr w v) →
      ∀ ρ : M.Ty P, Polynomial.aeval C (p ρ) =
        (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2))).starProjection

def Assembly : Prop := FrameLoc → CapSmooth → EigOrth → Lagrange → PRho.PRhoExists

theorem pRhoExists_of_cut (hA : Assembly) (hF : FrameLoc) (hC : CapSmooth) (hO : EigOrth) (hL : Lagrange) :
    PRho.PRhoExists :=
  hA hF hC hO hL

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
