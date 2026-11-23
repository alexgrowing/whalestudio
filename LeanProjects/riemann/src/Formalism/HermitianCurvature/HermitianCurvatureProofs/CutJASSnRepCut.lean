import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRho
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ebM (k r : ℕ) (v b : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Matrix.of fun p q => v p * herm (Hpk k r) (bvec q) b

section tht

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B')

def tht (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p) •
    sandw (QrD.ecOp π (ebM k r (Bw p) (SSn.prWv k r z a))) (QrD.ecOp π' (ebM k r (SSn.prWv k r z' a') (Bw' q)))

def thtA (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, conj (herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p)) •
    sandw (QrD.ecOp π (ebM k r (SSn.prWv k r z a) (Bw p))) (QrD.ecOp π' (ebM k r (Bw' q) (SSn.prWv k r z' a')))

end tht

def ThtFacts : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      (∀ a a' ι A B', B.hsInner (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι A) B' =
        B.hsInner A (thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι B')) ∧
      (∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z', ∀ a a' ι X,
        tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹)) ∧
        thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹))) ∧
      ∀ (c : ℂ) a a' ι, tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (c • a) (conj c • a') ι =
        (conj c) ^ 2 • tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι

def DatumUnit : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ), BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ (v : Fin S.f) (ζ : ℂ), (D.parOf S v).TT < Complex.normSq ζ →
      SSn.prWv S.G.k S.G.r (T v).base.z (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1 ∧
        SSn.prWv S.G.k S.G.r (T v).base.z' (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1

def ThtGaugeConst : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    PRho.Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k → ∀ l ∈ Finset.Icc 1 (S.G.k - 1),
    ∀ Bw Bw' : Fin S.G.k → Fin (2 * S.G.r + S.G.k + 1) → ℂ,
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z] Bw → Q.IsFrameOf S.G.k S.G.r [(T v).base.z'] Bw' →
      ∃ κ : M.Ty (D.parOf S v) → ℂ, ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ π ρ : M.Ty (D.parOf S v),
        M.Up (D.parOf S v) l π ρ →
        κ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw'
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ))) =
          ((Real.sqrt (M.Nrm (D.parOf S v) l π) : ℝ) : ℂ)

def SSnRepOfCut : Prop :=
  PRho.PRhoExists → PRho.GaugeLines → ThtFacts → DatumUnit → ThtGaugeConst → SSnRep

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
