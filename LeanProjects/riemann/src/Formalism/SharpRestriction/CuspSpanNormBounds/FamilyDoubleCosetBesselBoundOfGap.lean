import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.HermitianCurvature.BesselNonvanishingReduction

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.BridgeCS3d

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    PI.UpqRep.dsigW (k := k) (r := r) σ w v = Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW (k := k) (r := r) σ w v) =
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)
    rw [ih]
    rfl

theorem isBesselMapSm_iff {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (l : H → Wp) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π l ↔
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l := by
  simp only [PI.BesselMapUniq.IsBesselMapSm, Formalism.MainNotions.S.IsBesselMapSm, PI.BesselMapUniq.IsCWCont,
    Formalism.MainNotions.S.IsCWCont, dsigW_eq]
  exact Iff.rfl

def GapNearParameters (Cg0 : ℝ) : Prop :=
  ∀ (D : D7) (Ch Cg Cq : ℝ), Cg0 ≤ Cg → 1 ≤ Cq → ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ), NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ →
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast L.ε μ h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h

theorem c_ne_zero {D : D7} {Ch Cg Cq : ℝ} {L : LocBessel D.R.k D.R.rS} {lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ}
    {ka b κ : ℝ} (hN : NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ) : L.c ≠ 0 := by
  obtain ⟨hκ, hL, -, -⟩ := hN
  have hc : L.c = cOfDpsi (κ : ℂ) := hL.2.2.1
  have hka : 0 < ka := hL.2.2.2.2.2.1.2.2.2.1
  have hκ0 : κ ≠ 0 := by
    rcases hκ with h | h
    · rw [h]; exact one_ne_zero
    · rw [h]; exact hka.ne'
  rw [hc, cOfDpsi]
  have : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ0
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp [this, hI]

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.BridgeCS3d
