import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfInputs

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br

def localCorollaryConstant : ℝ := Classical.choose corollary_local_exists_constant

theorem local_corollary_of_de_rham (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR E1 E2 : ℝ) (hE1 : E1 = 800) (hE2 : localCorollaryConstant ≤ E2)
    (hDdR : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1)
    (h9 : Formalism.MainNotions.LocalSituation.adm9 D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) :
    Stmt D HW F Cm CR E1 E2 := by
  have h := Classical.choose_spec corollary_local_exists_constant
  intro hA
  subst hE1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hA
  obtain ⟨t1, c2, pr2, l3⟩ := a1
  have hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm := fun l _ K s LL hg => (t1 l K s LL hg).2.2.1
  have hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.1
  have hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.2.1
  have hP6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.2.2.1
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.2.2.2.2.2.1
  have hP2a : Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F := fun l _ K s LL hg => (pr2 l K s LL hg).1
  have r := h D HW F Cm CR hP3 hP4 hP5 hP6 hP9 hP2a l3 a3 a4 a7 a8 a9 a10 a12 a14 hDdR h9 hFont hUG
  exact ⟨r.1, r.2 E2 hE2⟩

end Formalism.MainNotions.N.Ln03
