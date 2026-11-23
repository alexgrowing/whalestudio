import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevYZero

open Formalism.IndefR.Lev Formalism.L2.DIV

theorem lev_datY_zero {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (r t : ℕ) (hr : r ≤ V.rank) (hn : V.rank = r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ ξ) (hL : L = datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (g : GL (Fin V.rank) (Lev.EAf D))
    (hU : g ∈ UA D.sp.cm V.gram) :
    (g ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ g ∈ St β ∧ (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H) ∧
      ∀ h : (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H, levFn β L g = P.chi ⟨_, h⟩ := by
  subst hL
  have hP : (datY (D := D) V.rank r t 0 hr Pg ∅ P χ ξ Frm.B).P = P := by simp [datY]
  constructor
  · rw [mem_lev, mem_parLev]
    constructor
    · rintro ⟨⟨-, hS, -, -⟩, hH⟩
      refine ⟨hS, ?_⟩
      rw [hP] at hH
      exact hH
    · rintro ⟨hS, hH⟩
      refine ⟨⟨hU, hS, fun PP _ => ?_, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
      · rw [mem_blockTri]
        intro i j hij
        exfalso
        have hi : (i : ℕ) < r := hn ▸ i.2
        have hj : (j : ℕ) < r := hn ▸ j.2
        simp [datY, blkOf, hi, hj] at hij
      · show rTup β _ g ∈ _
        rw [hP]
        exact hH
  · intro h
    unfold levFn
    change ext1 P.H P.chi (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) * _ * _ = _
    simp only [datY, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    exact extendOne_of_mem _ h

end GlobalTheory.LevYZero
