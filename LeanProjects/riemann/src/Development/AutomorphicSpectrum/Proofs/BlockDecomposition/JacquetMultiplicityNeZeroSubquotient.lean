import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JmSub

theorem exists_subQuot_of_jm_ne_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), Zc.jm x hd π ≠ 0 →
      ∃ S T : Subrepresentation (jac (stdBlocks (fun a => (x a).1) hd) π),
        Nonempty ((subQuot S T).Equiv (piTensor fun a => (x a).rep)) := by
  intro k _ _ _ _ h N x hd V _ _ π hjm
  obtain ⟨r, hr, hpos⟩ : ∃ r, GlobalTheory.SmGL.OccursTimes (GlobalTheory.SmGL.piTensor fun a => (x a).rep)
      (GlobalTheory.SmGL.jac (GlobalTheory.SmGL.stdBlocks (fun a => (x a).1) hd) π) r ∧ 0 < r := by
    by_contra hcon
    apply hjm
    unfold Zc.jm GlobalTheory.SmGL.jhMult
    refine le_antisymm (iSup_le fun r => iSup_le fun hr' => ?_) zero_le
    have hr0 : r = 0 := by
      by_contra hne
      exact hcon ⟨r, hr', Nat.pos_of_ne_zero hne⟩
    simp [hr0]
  obtain ⟨S, T, -, -, hST⟩ := hr
  exact ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hST ⟨0, hpos⟩⟩

end GlobalTheory.CompanionTheory.JmSub
