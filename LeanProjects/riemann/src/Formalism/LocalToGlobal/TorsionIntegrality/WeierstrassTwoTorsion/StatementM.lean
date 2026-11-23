import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def ZMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [CharZero K] [Field L] [CharZero L] (φ : K →+* L)
    (W : WeierstrassCurve K),
    PowerSeries.map φ (logSer W) = logSer (W.map φ) ∧
    PowerSeries.map φ (expSer W) = expSer (W.map φ) ∧
    PowerSeries.map φ (wpReg W) = wpReg (W.map φ) ∧
    φ (g₂ W) = g₂ (W.map φ) ∧ φ (g₃ W) = g₃ (W.map φ)

def DiscRel : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    g₂ W ^ 3 - 27 * g₃ W ^ 2 = W.Δ

def ChainNeg : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (f : R⟦X⟧),
    D W (f.subst (iSer W)) = -(D W f).subst (iSer W)

def ChainZSer : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℤ),
    D W (zSer W n) = C (n : R) * (fw W).subst (zSer W n) ∧
    (om W).subst (zSer W n) * derivative R (zSer W n) = C (n : R) * om W ∧
    ∀ f : R⟦X⟧, D W (f.subst (zSer W n)) = C (n : R) * (D W f).subst (zSer W n)

def ChainFgl : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (f : R⟦X⟧),
    (fw W).subst (U₁ : MvPowerSeries (Fin 2) R) * MvPowerSeries.pderiv R 0 (f.subst (fgl W))
      = (D W f).subst (fgl W) ∧
    (fw W).subst (U₂ : MvPowerSeries (Fin 2) R) * MvPowerSeries.pderiv R 1 (f.subst (fgl W))
      = (D W f).subst (fgl W)

def ConstOfD : Prop :=
  ∀ (R : Type u) [CommRing R] [IsAddTorsionFree R] (W : WeierstrassCurve R),
    (∀ f : R⟦X⟧, D W f = 0 → f = C (constantCoeff f)) ∧
    (∀ f : LaurentSeries R, dL f = 0 → f = HahnSeries.C (f.coeff 0)) ∧
    (∀ f : LaurentSeries R, DL W f = 0 → f = HahnSeries.C (f.coeff 0))

def JetZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (f : K⟦X⟧) (n : ℕ),
    (n.factorial : K) * coeff n (f.subst (expSer W)) = constantCoeff ((D W)^[n] f)

def JetMem : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (S : Subring K),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n, coeff n (D W f) ∈ S) ∧
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n : ℕ,
      (n.factorial : K) * coeff n (f.subst (expSer W)) ∈ S) ∧
    ∀ n : ℕ, (n.factorial : K) * coeff n (expSer W) ∈ S

def WpPrimeShape : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    dL (wpL W) = -2 * uPow (-3) + toL (derivative K (wpReg W)) ∧
    toL ((wSer W).subst (expSer W)) * yZ W = -1

end Formalism.L2.Th1.A
