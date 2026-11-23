import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.UnitNorm

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

def GapAndSizeRange (D : D7) (Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (p : ℕ) : Prop :=
  AllGaps L.lam (Cg * p * ((2 * D.R.rS + 2 : ℕ) : ℝ)) ∧
    (((D.R.rS + 1) * (p + D.R.rS + 2) : ℕ) : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u L.lam

def InBig {k r : ℕ} (L : LocBessel k r) (q : (Fin r → ℂ) × ℂ) : Prop :=
  (∀ i, q.1 i ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq q.2

end PI.UnitNorm

namespace PI

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.UnitNorm

def UnitNorm (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Mx D.R.k D.R.rS → (H →L[ℂ] H)), IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) σ' →
    ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
      (∃ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q ∧ L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) ≠ 0) →
      ∃ f'' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f'' ∧ jNorm2 L f'' μsec ≠ 0 ∧ jNorm2 L f'' μsec ≠ ⊤

end PI
