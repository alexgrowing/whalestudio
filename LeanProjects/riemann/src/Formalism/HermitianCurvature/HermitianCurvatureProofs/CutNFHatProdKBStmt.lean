import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def OmKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ∧
    ∀ a : Fin P.r, Formalism.QuantumDeterminants.Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def FFKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :=
  Q.FFl P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' 0 (OmKB p)

def IsGaugeQQKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
    CutMP.Gauge.FamR P p.T.base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e
          (Q.QL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (fun ρ' => MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e Φ ρ')) ρ

end kb

def NFHatProdKBS : Prop :=
  ∃ C₁ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameKB p e → IsGaugeQQKB p e → MA.IsModelLevel P (MA.DQ P) L → ∀ (N : ℕ) (u : List (MA.A P (MA.DQ P))),
      u.length ≤ N → (∀ a ∈ u, a ∈ MA.hatSet P L) →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
        (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ k, NFOpOK C₁ p N (Th k)) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          B.JF p.T.base F ∈ FFKB p →
          MA.actA P u.prod (trJKB p e (B.JF p.T.base F)) =
            ∑ k, MA.actA P (b k) (trJKB p e (B.JF p.T.base (B.opApply (Th k) F)))

def NFHat1KB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameKB p e → IsGaugeQQKB p e → MA.IsModelLevel P (MA.DQ P) L →
    ∀ X ∈ MA.hatSet P L,
      ∃ ts : List (MA.A P (MA.DQ P) × B.DiffOp P.k P.r Wp Wq),
        (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet P L) ∧
          CutMP.PolyOp (2 * P.r + P.k + 1) ((P.r + 1) * (2 * P.r + P.k + 1)) t.2 ∧
          B.Commutes p.T.base (B.GPos p.T.base) t.2) ∧
        ∀ J ∈ FFKB p, MA.actA P X (trJKB p e J) = (ts.map fun t => MA.actA P t.1 (trJKB p e (B.opApply t.2 J))).sum

def NFJCommKB : Prop :=
  ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Θ : B.DiffOp P.k P.r Wp Wq) (d A : ℝ), 0 ≤ d →
    B.SmoothCoef (B.GPos p.T.base) Θ → B.Commutes p.T.base (B.GPos p.T.base) Θ → CutMP.GlobCoef Θ d →
    Cc * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r ^ 2 + 6 * (P.r : ℝ) * (B.opOrder Θ : ℝ) + d ≤ A →
    ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      B.JF p.T.base F ∈ FFKB p →
      B.JF p.T.base (B.opApply Θ F) ∈ FFKB p ∧
        ∀ x ∈ MA.Qset P.r P.TT,
          B.opApply Θ (B.JF p.T.base F) (B.gq p.T.base x) = B.JF p.T.base (B.opApply Θ F) (B.gq p.T.base x)

def NFPolyComp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o₁ κ₁ o₂ κ₂ : ℕ)
    (Θ₁ Θ₂ : B.DiffOp k r Wp Wq), CutMP.PolyOp o₁ κ₁ Θ₁ → CutMP.PolyOp o₂ κ₂ Θ₂ →
    ∃ Θ : B.DiffOp k r Wp Wq, CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      (∀ Bs : B.RealPlaceData k r Wp Wq, B.Commutes Bs (B.GPos Bs) Θ₁ → B.Commutes Bs (B.GPos Bs) Θ₂ →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (B.GV k r) F → ∀ g ∈ B.GV k r,
        B.opApply Θ F g = B.opApply Θ₁ (B.opApply Θ₂ F) g

def NFPolyId : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    ∃ Θ : B.DiffOp k r Wp Wq, CutMP.PolyOp 0 0 Θ ∧ (∀ Bs : B.RealPlaceData k r Wp Wq, B.Commutes Bs (B.GPos Bs) Θ) ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), B.opApply Θ F g = F g

def NFPolySmul : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq)
    (c : ℂ), CutMP.PolyOp o κ Θ →
    ∃ Θ' : B.DiffOp k r Wp Wq, CutMP.PolyOp o κ Θ' ∧
      (∀ Bs : B.RealPlaceData k r Wp Wq, B.Commutes Bs (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ') ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), B.opApply Θ' F g = c • B.opApply Θ F g

end

end Formalism.FourierDecayAlt.P.CutBP
