import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelabDR

theorem letters_getElem?_wholeL {D : D7} (O : Setup D) (k : Fin (D.R.f * O.N)) :
    (letters O.S.Dw)[(k : ℕ)]? = some (wholeL O k) := by
  have hk : (k : ℕ) < (letters O.S.Dw).length := by
    rw [GlobalTheory.ShFam.Pad.length_letters O.S]; exact k.2
  rw [List.getElem?_eq_getElem hk]
  rfl

theorem fam_eq_single : ∀ (D : D7) (O : Setup D), (∀ i, GlobalTheory.RelabDR.sg O i = 1 ∨ GlobalTheory.RelabDR.sg O i = -1) ∧ ∀ (R : ℝ) (i : GlobalTheory.EigWhole.Var O), (∃ z, GlobalTheory.RelabDR.ix O i = .inl z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inl (z.1, (z.2 : ℕ))) (GlobalTheory.RelabDR.sg O i)) ∨ ∃ z k, GlobalTheory.RelabDR.ix O i = .inr z ∧ (letters O.S.Dw)[k]? = some z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inr k) (GlobalTheory.RelabDR.sg O i) := by
  intro D O
  refine ⟨?_, ?_⟩
  · rintro (x | k | k)
    · show rootSg O x = 1 ∨ rootSg O x = -1
      unfold rootSg
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro R (⟨t, i⟩ | k | k)
    · refine Or.inl ⟨rootL O (t, i), rfl, ?_⟩
      have hp' := O.S.p_eq
      have hq := O.S.rank_eq
      show rootSym O.S.Dw (ArIn.ind ∅) (some R) (DV.tauEmb D t) i = Finsupp.single _ (rootSg O (t, i))
      unfold rootSym rootSg
      dsimp only
      by_cases hi : (i : ℕ) < O.j
      · have hx : ((rootL O (t, i)).1, ((rootL O (t, i)).2 : ℕ)) = (DV.tauEmb D t, (i : ℕ)) := by
          unfold rootL LieGen.rootLetter
          rw [dif_pos hi]
        rw [if_pos (show (i : ℕ) < O.S.Dw.p by omega), if_pos hi, hx]
      · have hx : ((rootL O (t, i)).1, ((rootL O (t, i)).2 : ℕ)) =
            (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t), O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ)) := by
          unfold rootL LieGen.rootLetter
          rw [dif_neg hi]
          simp only [Prod.mk.injEq, true_and]
          omega
        rw [if_neg (show ¬ (i : ℕ) < O.S.Dw.p by omega), if_neg hi, hx]
    · exact Or.inr ⟨wholeL O k, k, rfl, letters_getElem?_wholeL O k, rfl⟩
    · exact Or.inr ⟨wholeL O (Fin.rev k), (Fin.rev k : ℕ), rfl, letters_getElem?_wholeL O _, rfl⟩

end GlobalTheory.RelabDR

end
