import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTie
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneF

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

theorem rows_rdE_pos (D : D7) : 0 < D.host.rdE := by
  unfold Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _

def FamilyGramHypotheses : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    wordPairNormRelation (X x hx i) u u' ∧ @LatticeDeterminantFactorization (Fm.D x i) (X x hx i) u u' ∧
      wordPairEntriesInLattice (X x hx i) u u' ∧ wordPairTermInjective (X x hx i) (Y x hx i u u')

theorem family_gram_facts_of_hypotheses (h : FamilyGramHypotheses Fm C1 X Y) : rows_TiesF Fm C1 X Y := fun x hx i u u' =>
  ⟨rows_TermPtsTie_of _ (rows_rdE_pos _) (h x hx i u u').1, (h x hx i u u').2.1, (h x hx i u u').2.2.1⟩

theorem family_gluing_bounds_of_beta (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hAmp : FamilyAmplitudeBounds Fm C1) (hT : FamilyGramHypotheses Fm C1 X Y)
    (hBL : ∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') : RowsF Fm C1 X Y :=
  rows_RowsF_of_one Fm C1 X Y hAdm (amplitude_bounds_of_family_amplitude_bounds Fm C1 hAmp) (family_gram_facts_of_hypotheses Fm C1 X Y hT)
    (rows_OneF_of Fm C1 X Y hAdm hAmp (family_gram_facts_of_hypotheses Fm C1 X Y hT) (fun x hx i u u' => (hT x hx i u u').2.2.2) hBL)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
