import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.PlanePure

theorem schwartzBruhat2_eq_sum_pt : Ad3.SchwartzSpaceL2.SPure := by
  intro F _ _ _ _ _ _ φ hφ
  have hφ' : φ ∈ GJMatrix.localSchwartzBruhatPi F (ι := Fin 2) := hφ
  clear hφ
  rw [GJMatrix.localSchwartzBruhatPi_eq_span] at hφ'
  induction hφ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨N, a⟩, rfl⟩ := hx
    refine ⟨1, fun _ => GJMatrix.cosetInd (valBall F N) (a 0),
      fun _ => GJMatrix.cosetInd (valBall F N) (a 1),
      fun _ => ⟨GJMatrix.cosetInd_valBall_mem N _, GJMatrix.cosetInd_valBall_mem N _⟩, ?_⟩
    funext y
    simp [GJMatrix.localTensor, pt, Fin.prod_univ_two]
  | zero =>
    exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, f, g, hfg, rfl⟩ := ihx
    obtain ⟨m, f', g', hfg', rfl⟩ := ihy
    refine ⟨n + m, Fin.append f f', Fin.append g g', ?_, ?_⟩
    · intro i
      induction i using Fin.addCases with
      | left i => simpa using hfg i
      | right i => simpa using hfg' i
    · rw [Fin.sum_univ_add]
      simp
  | smul c x _ ih =>
    obtain ⟨n, f, g, hfg, rfl⟩ := ih
    refine ⟨n, fun i => c • f i, g, fun i => ⟨Submodule.smul_mem _ c (hfg i).1, (hfg i).2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext y
    simp [pt, mul_assoc]

end GlobalTheory.CompanionTheory.PlanePure
