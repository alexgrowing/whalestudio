import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra

namespace GlobalTheory.AdjoinStableCommutes

theorem adjoin_stable_and_commutes {E V G : Type} [Field E] [AddCommGroup V] [Module E V]
    (A : Set GlobalTheory.KZ.Letter) (f : GlobalTheory.KZ.Letter → Module.End E V) (W : Submodule E V)
    (g : G → Module.End E V)
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W)
    (hg : ∀ T ∈ A, ∀ (s : G), ∀ x ∈ W, f T (g s x) = g s (f T x)) :
    ∀ Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A), ∀ x ∈ W,
      (FreeAlgebra.lift E f Q) x ∈ W ∧
        ∀ s : G, g s ((FreeAlgebra.lift E f Q) x) = (FreeAlgebra.lift E f Q) (g s x) := by
  intro Q hQ
  induction hQ using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro x hx
    rw [FreeAlgebra.lift_ι_apply]
    exact ⟨hW T hT x hx, fun s => (hg T hT s x hx).symm⟩
  | algebraMap r =>
    intro x hx
    rw [AlgHom.commutes]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hx
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add a b _ _ ha hb =>
    intro x hx
    rw [map_add]
    refine ⟨?_, fun s => ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (ha x hx).1 (hb x hx).1
    · rw [LinearMap.add_apply, LinearMap.add_apply, map_add, (ha x hx).2 s, (hb x hx).2 s]
  | mul a b _ _ ha hb =>
    intro x hx
    rw [map_mul]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.End.mul_apply]
      exact (ha _ (hb x hx).1).1
    · rw [Module.End.mul_apply, Module.End.mul_apply, (ha _ (hb x hx).1).2 s, (hb x hx).2 s]

end GlobalTheory.AdjoinStableCommutes
