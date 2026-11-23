import Mathlib
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff

theorem UpperTheory.Reformulated.B.Qj25.inSpan_add :
    ∀ {R : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {what₂ : Formalism.BasicNotions.Rows.Data R}
    (N : Formalism.BasicNotions.NData R H what₂) {i : N.Loc} {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i))
    (rep : X' → Formalism.MainNotions.N.GE N →* Formalism.MainNotions.N.MatN N i) {a b : X' → Formalism.MainNotions.N.MatN N i},
    Formalism.MainNotions.N.InSpan N i T' rep a →
      Formalism.MainNotions.N.InSpan N i T' rep b →
        Formalism.MainNotions.N.InSpan N i T' rep
          (a +
            b) := by
  intro R H what₂ N i X' T' rep a b ha hb
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  obtain ⟨n, f', g', hf', rfl⟩ := hb
  refine ⟨m + n, Fin.append f f', Fin.append g g', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact hf j
    · rw [Fin.append_right]; exact hf' j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
