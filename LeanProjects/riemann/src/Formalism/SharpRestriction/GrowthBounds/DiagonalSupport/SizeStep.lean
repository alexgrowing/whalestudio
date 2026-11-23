import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SizeStepAlt

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem sizeStep : ∃ CDn C₁ : ℝ, 0 < CDn ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ [NeZero F.J],
      SizeAt (K := K) p F (fun j : ZMod F.J => (F.LLset (segZ j)).card) (dT TT lam0)
        (CDn * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) ∧
      (∀ (j : ZMod F.J) (u : ℕ), u < (fun j : ZMod F.J => (F.LLset (segZ j)).card) j + r →
        3 / 8 * slU F p (flatDeg lam0) Y (r + K) (fun j : ZMod F.J => (F.LLset (segZ j)).card) j u <
          Bo p F (flatDeg lam0) (segZ j) (posU F ((fun j : ZMod F.J => (F.LLset (segZ j)).card) j) (segZ j) u) / 2) ∧
      1 ≤ cPrime n' r TT.card c0 cpp cStar ∧ 1 ≤ F.J :=
  sizeStep'

end Formalism.MainNotions.Proposition5Numerics
