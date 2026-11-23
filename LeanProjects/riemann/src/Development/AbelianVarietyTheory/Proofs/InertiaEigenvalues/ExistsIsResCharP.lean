import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCycOInvPow

noncomputable section
namespace GlobalTheory.TopSteps
open GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.PhiGam Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem exists_topSit {l : ℕ} [Fact l.Prime] (hl : 17 ≤ l) (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) : ∃ S : TopSit P, S.r = 1 ∧ S.n = 1 ∧ S.D.t = 2 := by
  obtain ⟨K, LL, emb, D, Γ, ht, h⟩ :=
    GlobalTheory.AdmLoc.CycWitness.exists_premises_block hl P AI hT 2 (by norm_num) (by norm_num)
  exact ⟨{ K := K, LL := LL, n := 1, r := 1, emb := emb, D := D, Γ := Γ, hyp := h }, rfl, rfl, ht⟩

end GlobalTheory.TopSteps
