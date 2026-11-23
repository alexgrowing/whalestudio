import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasicsOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def castZp {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) : ℤ_[a] →+* ℤ_[b] := by
  subst e; exact RingHom.id _

theorem castZp_symm {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) (x : ℤ_[b]) :
    castZp e (castZp e.symm x) = x := by
  subst e; rfl

theorem castZp_val {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) (x : ℤ_[a]) :
    (castZp e x).valuation = x.valuation := by
  subst e; rfl

theorem castZp_inj {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) :
    Function.Injective (castZp e) := by
  subst e; exact fun x y h => h

def levBasics_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hGen : GenUnitsC) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
    (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ) :
    LevBasics ((HW l).W K 1 LL h.2.2) a s := by
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI hpF : Fact ((D.loc l).PD K).p.Prime := ⟨by rw [e]; exact Fact.out⟩
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := OLC.complete_max LL
  haveI : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  letI : Algebra ℤ_[((D.loc l).PD K).p] ↥(OL LL) :=
    ((algebraMap ℤ_[l] ↥(OL LL)).comp (castZp e)).toAlgebra
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL h.2.2) :=
    Formalism.MainNotions.UnusedSlot80.ring_condition_uniformizer_polynomial D HW F hP9 l K LL h
  have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [e]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
  have hZinj : Function.Injective (algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL)) :=
    (Formalism.MainNotions.LiftingTheory.zl_inj_O LL).comp (castZp_inj e)
  have hχ : ∀ g : ((HW l).W K 1 LL h.2.2).Gam, ∃ z : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨z, hz⟩ := Formalism.MainNotions.LiftingTheory.chi_zl (P := D.loc l) (H := HW l) h.2.2 g
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_⟩
    show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
    rw [castZp_symm, hz]
  have hγz : ∃ z0 : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z0 : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) ∧
      ((z0 : ℤ_[((D.loc l).PD K).p]) - 1).valuation = 1 := by
    obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (P := D.loc l) (H := HW l) h.2.2
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_, ?_⟩
    · show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
      rw [castZp_symm, hz]
    · have : ((Units.map (castZp e.symm).toMonoidHom z : ℤ_[((D.loc l).PD K).p]ˣ) :
          ℤ_[((D.loc l).PD K).p]) - 1 = castZp e.symm ((z : ℤ_[l]) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, castZp_val, hv]
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F hP9 l K LL h
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [e]; exact h.2.1
  letI : Algebra ↥(OL LL) (AlgebraicClosure ↥LL.1) :=
    ((algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).comp (algebraMap ↥(OL LL) ↥LL.1)).toAlgebra
  have hinjF : Function.Injective (algebraMap ↥(OL LL) (AlgebraicClosure ↥LL.1)) :=
    (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective.comp Subtype.val_injective
  haveI : CharZero (AlgebraicClosure ↥LL.1) :=
    charZero_of_injective_algebraMap (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective
  exact levBasics_of ((HW l).W K 1 LL h.2.2) hlm (AlgebraicClosure ↥LL.1) hR hinjF hZinj hχ hγz
    (by rw [hcard, e]) hp2 hGen a s

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
