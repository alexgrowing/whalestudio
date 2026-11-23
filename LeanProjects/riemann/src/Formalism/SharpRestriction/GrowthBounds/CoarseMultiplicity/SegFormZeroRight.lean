import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem famOK_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {C0 CE1 CE2 Cm : ℝ} {X : Loc}
    [NeZero X.m] {β : GlobalTheory X} {u : Vecs O C0 CE1 CE2 X} (h : FamOK O C0 CE1 CE2 Cm X β u) {j : Fin (numSeg X.TT)}
    (hj : ¬ Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) : u j = 0 := by
  obtain ⟨hL, hz⟩ := h j
  funext b
  by_cases hb : b = β j
  · subst hb
    have hm := (Submodule.mem_pi.mp hL) (β j) (Set.mem_univ _)
    rw [if_neg hj] at hm
    simpa using hm
  · exact hz b hb

theorem segForm_zero_left {O : Type} [CommRing O] [IsDomain O] {p r s : ℕ} (S : SegData s)
    (g : SegVs O r s S.t) : segForm O p r S 0 g = 0 := by
  unfold segForm fock
  simp

end Formalism.MainNotions.ColumnSystems.Pf
