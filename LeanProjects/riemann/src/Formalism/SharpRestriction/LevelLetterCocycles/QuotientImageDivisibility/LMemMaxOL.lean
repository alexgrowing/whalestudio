import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpCritPOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemKD

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem l_mem_maxOL {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) [IsLocalRing ↥(OL LL)] :
    ((l : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨w, hw⟩
  have hv := P.v_l LL
  have h1 := (P.v_O LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))).2 (w : ↥(OL LL)).2
  have h2 := (P.v_O LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)))).2
    ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2
  have h3 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
      P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
  have h4 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0 :=
    le_antisymm (le_trans (le_add_of_nonneg_right h2) h3.le) h1
  rw [hw, map_natCast] at h4
  rw [h4] at hv
  exact zero_ne_one hv

set_option maxHeartbeats 800000 in

theorem expCrit_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F)
    (hB : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hg))
    (hCpl : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) [IsLocalRing ↥(OL LL)],
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL)) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL hA' h5
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI := hCpl l LL
  have h1 := hA.1 l K 1 LL hA'.2.2
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1
  have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact l_mem_maxOL (D.loc l) LL
  have tie := ((Cm l).C K 1 LL hA'.2.2).tie
  exact expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL) h1.1 h1.2.2.1
    (hL l K LL hA' h5) h1.2.2.2.2.1 h1.2.2.2.2.2.2.2.2.1 h11.2.2 (hB l K LL hA'.2.2) tie
    h1.2.2.2.1 (ptTrans_rec D HW F hP9 l K LL hA' h5)

end Formalism.MainNotions.N.Pv.LocalLengthBound
