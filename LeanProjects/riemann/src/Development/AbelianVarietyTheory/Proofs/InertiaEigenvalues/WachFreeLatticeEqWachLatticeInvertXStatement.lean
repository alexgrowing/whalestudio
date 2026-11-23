import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFreeLatticeEqWachLatticeInvertX
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFreeLattice_eq_wachLattice_invert_X : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ N₁ : Submodule (AA K LL) (W.DD T), FreeA W T N₁ → IsBaseChange W.EE N₁.subtype → (∀ x ∈ N₁, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ N₁) → (∀ y ∈ N₁, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T N₁) → ∃ a : ℕ, (∀ x ∈ N₁, W.X ^ a • x ∈ W.N T) ∧ ∀ x ∈ W.N T, W.X ^ a • x ∈ N₁ := by
  first | exact @GlobalTheory.NL.InvX.main | exact GlobalTheory.NL.InvX.main | (intros; apply GlobalTheory.NL.InvX.main <;> assumption)
