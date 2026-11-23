import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.RowExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreSteps

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

theorem zz_smul (pr : P →* Q) {n : ℕ} (r : ℝ) (b : (Fin n → Q) → ℝ) (a c : ℕ) :
    zz pr (r • b) a c = r • zz pr b a c := rfl

theorem Wtop_smul (pr : P →* Q) {n : ℕ} (r : ℝ) (b : (Fin n → Q) → ℝ) :
    Wtop pr (r • b) = r • Wtop pr b := rfl

theorem QC.smul {n : ℕ} {b : (Fin (n + 1) → Q) → ℝ} (hb : QC b) (r : ℝ) : QC (r • b) := by
  refine ⟨fun g x => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hb.1 g x]
  · rw [dc_smul, hb.2, smul_zero]

def GoodS (pr : P →* Q) {p q : ℕ} (x : Bi P Q (p + 2) (q + 2)) : Prop :=
  ∃ n : ℕ, n = p + q + 2 ∧ ∃ b : (Fin (n + 1) → Q) → ℝ, QC b ∧
    ∃ (w : Bi P Q (p + 1) (q + 2)) (e : Bi P Q (p + 2) (q + 1)),
    PInv pr w ∧ dv w = 0 ∧ PInv pr e ∧ dh e = 0 ∧ x = dh (zz pr b (p + 1) (q + 2)) + dh w + dv e

def GoodT (pr : P →* Q) {q : ℕ} (x : Bi P Q 1 (q + 2)) : Prop :=
  ∃ b : (Fin (q + 2) → Q) → ℝ, QC b ∧ ∃ e : Bi P Q 1 (q + 1), PInv pr e ∧ dh e = 0 ∧ x = Wtop pr b + dv e

section Rec

variable (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g)
include hs

end Rec

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
