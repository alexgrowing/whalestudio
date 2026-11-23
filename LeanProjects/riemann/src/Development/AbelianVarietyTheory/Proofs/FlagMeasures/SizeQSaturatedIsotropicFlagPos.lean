import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FgOfHtNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem satIn_of_trace (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (h : ∀ y, y ∈ S ↔ y ∈ lamX I x ∧ y ∈ Submodule.span I.E (S : Set (Fin I.n → I.E))) :
    GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S := by
  have := GlobalTheory.StepDualityCompare.totallyComplex I

  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span I.E (S : Set (Fin I.n → I.E)))
  let φ : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E) := q.subtype ∘ₗ Submodule.linearProjOfIsCompl q _ hq.symm
  have hker : LinearMap.ker φ = Submodule.span I.E (S : Set (Fin I.n → I.E)) := by
    rw [LinearMap.ker_comp_of_ker_eq_bot _ q.ker_subtype]
    exact Submodule.linearProjOfIsCompl_ker _
  have hX : ∀ v, IsUnit (frm I x v).det := GlobalTheory.StepDualityCompare.frm_det I x
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat := (Formalism.HN.htImage I.E (Fin I.n → I.E) (Fin I.n) (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x)
    (bas I) (frm I x) hX hX φ (lamX I x) hfg).1
  have hS : lamX I x ⊓ (LinearMap.ker φ).restrictScalars (𝓞 I.E) = S := by
    ext y
    rw [hker, Submodule.mem_inf, Submodule.restrictScalars_mem, h]
  rw [hS] at hsat
  exact hsat

theorem sizeQ_flag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  intro I x a j S hS i
  obtain ⟨-, hmono, -, htr, -⟩ := hS
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x (S i.castSucc) := satIn_of_trace I x _ (htr i.castSucc)
  have hle : S i.succ ≤ lamX I x := fun y hy => ((htr i.succ y).1 hy).1
  have hmn : S i.castSucc ≤ S i.succ := hmono (Fin.castSucc_le_succ i)
  have hpos := GlobalTheory.StepDualityCompare.htQ_pos I x hfg _ _ hsat hle hmn
  unfold Formalism.HN.sizeQ
  exact Real.rpow_pos_of_pos hpos _

end GlobalTheory.LeviIso
