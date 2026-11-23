import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ListSumSplittings

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def ThChain (Ψ : ℕ → ℝ → ℝ) : Prop := ∀ (n : ℕ) (x : ℝ), 0 < x → HasDerivAt (Ψ n) (Ψ (n + 1) x / x) x

section leibterm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def LeibTerm (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq) (T' : B.DTerm k r Wp Wq) : Prop :=
  ∃ T ∈ Dop, ∃ (P : B.Mat k r → ℂ) (j : ℕ), ListSumSplittings.PolyClass ((2 * r + 2) * T.word.length) P ∧
    T'.word.Sublist T.word ∧
    ∀ g ∈ C6.domL Bs ∅, T'.coef g = (P g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ j) • T.coef g

end leibterm

def NFLeibExp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) →
    ∃ terms : List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
              ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x)).sum

def NFLeibOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq),
    B.SmoothCoef (C6.domL Bs ∅) Dop →
    ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp k r Wp Wq),
      (∀ q, B.SmoothCoef (C6.domL Bs ∅) (L q)) ∧ (∀ q, ∀ T' ∈ L q, LeibTerm Bs Dop T') ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.opApply Dop (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (L q) F x

def NFLeibBd : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (nf : ℕ)
    (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq) (o κ : ℕ) (Dop : B.DiffOp k r Wp Wq),
    (∀ j, C6.FibBound Bs (fib j)) → C6.InDDPlus Bs fib ∅ o κ Dop →
    ∀ L : B.DiffOp k r Wp Wq, (∀ T' ∈ L, LeibTerm Bs Dop T') →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖B.opApply L F g‖ ≤ K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A)

def NFVLin : Prop :=
  ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (Q : ℕ) (c : Fin (Q + 1) → ℝ → ℂ)
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (Hq : Fin (Q + 1) → B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    (∀ q, ContinuousOn (Hq q) (B.GPos Bs)) →
    (∀ q, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g → ‖Hq q g‖ ≤ C * B.gN g ^ (-A)) →
    (∀ g ∈ B.GPos Bs, H g = ∑ q, c q (Gf k r Bs.z Bs.z' g) • Hq q g) →
    ∀ γ : C.LPt, D.IsLocPt γ (r + 1) → 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ →
      D.vecV Bs ν' m₀ H γ = ∑ q, c q (D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ) • D.vecV Bs ν' m₀ (Hq q) γ

end

end Formalism.FourierDecayAlt.P.CutBP
