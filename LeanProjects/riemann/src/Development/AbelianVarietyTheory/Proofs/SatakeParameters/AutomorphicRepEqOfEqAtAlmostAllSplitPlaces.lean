import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary

namespace GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isoLoc_perm {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) : isoLoc N A Pa w = isoLoc N A Pa' w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l =>
    simp only [List.foldr_cons]
    rw [← A.lpSum_assoc, ← A.lpSum_assoc, A.lpSum_comm (spehLoc N A y w)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.RowTie.repDet_split : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i →
    ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  intro R H what₂ N A i hBC hSp hRep P P' hP
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hperm := hSp P P' hP Pa Pa' hPa hPa'
  have hiso := GlobalTheory.RowTie.RepDet.isoLoc_perm N A hperm
  apply hRep P P'
  · intro w hw
    rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw, hiso w]
  · intro w hw
    rw [← (hPa.2.2.2.2.1 w hw).2, ← (hPa'.2.2.2.2.1 w hw).2, hiso w]
