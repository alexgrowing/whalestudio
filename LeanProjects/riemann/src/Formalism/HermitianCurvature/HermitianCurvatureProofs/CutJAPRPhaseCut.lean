import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

def cW (k r : ℕ) (θ : ℝ) : Q.Mx k r :=
  B2.embWb k r (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))

def PhaseSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ θ : ℝ, ∃ h h' : Q.Mx k r, h ∈ UWset k r z ∧ h' ∈ UWset k r z' ∧
      (∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
        h *ᵥ (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = Complex.exp (-((θ : ℂ) * Complex.I)) • (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) ∧
        (∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = 0 → h *ᵥ v = v) ∧
        CP.mu0 k r z z' (rot θ ζ) = h * cW k r θ * CP.mu0 k r z z' ζ * h') ∧
      ∀ v, inWb k r v → herm (Hpk k r) v z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v

def LowerUnipotentRotation : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (θ : ℝ) (Y : ℂ) (f : Q.Mx k r → E), ∀ g ∈ Q.Glev k r (Fin.last r),
      Q.tL k r z z' (Fin.last r) Y 1 0 f (cW k r θ * g) =
        Complex.exp (-((θ : ℂ) * Complex.I)) • Q.tL k r z z' (Fin.last r) Y 1 0 (fun x => f (cW k r θ * x)) g

def RotRadSp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ (θ : ℝ) (Φ : Q.Fn k r (Wq →L[ℂ] Wp)), Φ ∈ Q.RadSp k r z z' π π' →
      (fun c g => Φ c (cW k r θ * g)) ∈ Q.RadSp k r z z' π π'

def ThtRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ (θ : ℝ) (h h' : Q.Mx P.k P.r), h ∈ UWset P.k P.r Bs.z → h' ∈ UWset P.k P.r Bs.z' →
    ∀ ζ ∈ Gauge.GC.Ann P,
      h *ᵥ SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = Complex.exp (-((θ : ℂ) * Complex.I)) • SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z = 0 → herm (Hpk P.k P.r) v (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 →
        h *ᵥ v = v) →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v) →
      ∀ Xf : Wq →L[ℂ] Wp,
        (Bs.π h).comp (((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) Xf).comp (Bs.π' h')) =
          Complex.exp ((θ : ℂ) * Complex.I) • (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) ((Bs.π h).comp (Xf.comp (Bs.π' h')))

def PhaseInvOfCut : Prop :=
  PhaseSec → LowerUnipotentRotation → RotRadSp → ThtRot → KapLine → AlgSS → DatumConst → FibStable → PhaseInv

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
