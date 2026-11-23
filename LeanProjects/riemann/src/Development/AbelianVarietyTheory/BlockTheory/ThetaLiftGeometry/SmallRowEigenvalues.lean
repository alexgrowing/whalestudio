import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def RowEigSmall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) :
    Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)

theorem one_lt_normV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by
  unfold normV
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact Finite.one_lt_card

theorem rowEigSmall_of_le {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N)
    (h : ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
      ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
        ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)) :
    RowEigSmall N A := by
  intro i σ hσ w hw hu α hα
  have hrt : R.r < R.t := by have := R.rank_add_five_le; unfold Ranks.r; omega
  refine lt_of_le_of_lt (h i σ hσ w hw hu α hα) ?_
  have h1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have h2 : (R.r : ℝ) < (R.t : ℝ) := by exact_mod_cast hrt
  exact Real.rpow_lt_rpow_of_exponent_lt h1 (by linarith)

end GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
