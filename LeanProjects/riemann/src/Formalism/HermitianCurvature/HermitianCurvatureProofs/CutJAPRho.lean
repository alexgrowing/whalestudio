import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho

noncomputable section

def nrmW (k r : ℕ) (z a : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (herm (Hpk k r) (SSn.prWv k r z a) (SSn.prWv k r z a)).re

section spec

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def PRhoSpec (P : M.Par) (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp))
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pr ρ) {a | 1 / 4 < nrmW P.k P.r z a}) ∧
  (∀ h ∈ UWset P.k P.r z, ∀ ρ a, Pr ρ (h *ᵥ a) = (π h).comp ((Pr ρ a).comp (π h⁻¹))) ∧
  ∀ a, 0 < nrmW P.k P.r z a →
    (∀ ρ (c : ℂ), c ≠ 0 → Pr ρ (c • a) = Pr ρ a) ∧
    (∀ ρ x y, inner ℂ (Pr ρ a x) y = inner ℂ x (Pr ρ a y)) ∧
    (∀ ρ ρ', (Pr ρ a).comp (Pr ρ' a) = if ρ = ρ' then Pr ρ a else 0) ∧
    ∀ ρ (x : Wp), Pr ρ a x = x ↔
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [z, SSn.prWv P.k P.r z a] Fr →
        ∀ w : ℂ, Q.capRep P.k P.r π Fr w x = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • x

end spec

def PRhoExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ Pr, PRhoSpec P Bs.z Bs.π Pr

section ctx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Hyp (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  BuiltOW Cc S T f χ ν' m₀ top A₀ ∧ IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

end ctx

def GaugeLines : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k →
    ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ (ρ : M.Ty (D.parOf S v))
      (Fr : Fin (S.G.k - 1) → Fin (2 * S.G.r + S.G.k + 1) → ℂ),
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z, SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ] Fr →
      ∀ (w : ℂ) (x : Wq (S.pl v)),
        Q.capRep S.G.k S.G.r (T v).base.π Fr w (e ρ ζ x) =
          M.xC (D.parOf S v) ρ (w - ((S.G.k : ℂ) - 2) / 2) • e ρ ζ x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho
