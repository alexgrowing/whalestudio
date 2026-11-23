import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows

open Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes

def AgreeAtAlmostAllSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) : Prop :=
  {w : PlE H | IsSplitPl H w ∧ A.locG χ w ≠ A.locG χ' w}.Finite

def HeckeCharEqOfSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ χ χ' : A.CG 1, AgreeAtAlmostAllSplit A χ χ' → χ = χ'

theorem agreeAtAlmostAllSplit_iff {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) :
    AgreeAtAlmostAllSplit A χ χ' ↔
      ∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w := by
  simp only [AgreeAtAlmostAllSplit, Filter.eventually_cofinite, Classical.not_imp]

example {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ : A.CG 1) : AgreeAtAlmostAllSplit A χ χ := by
  simp [AgreeAtAlmostAllSplit]

theorem HeckeCharEqOfSplit.of_forall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    {A : NAut N} (h : HeckeCharEqOfSplit N A) (χ χ' : A.CG 1)
    (hw : ∀ w, IsSplitPl H w → A.locG χ w = A.locG χ' w) : χ = χ' :=
  h χ χ' ((agreeAtAlmostAllSplit_iff A χ χ').2 (Filter.Eventually.of_forall hw))

end GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
