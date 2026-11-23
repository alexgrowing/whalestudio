import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem ldtensor_blockAct_comp (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) :
    (blockAct K (n := n) g).comp (blockEmb K (k := k) (n := n) s) =
      (blockEmb K s).comp (rowAct K (g s)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [blockEmb, blockAct, rowAct, map_sum, rename_C]

theorem ldtensor_blockAct_blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) := by
  exact AlgHom.congr_fun (ldtensor_blockAct_comp K g s) F

theorem block_action_tensor : BlockActTensor := by
  intro R K _ _ _ S _ k n g
  refine ⟨fun s F => ldtensor_blockAct_blockEmb K g s F, ?_⟩
  intro M M' hMM' P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => rowAct K (g s) (F s), fun s => hMM' s (F s) (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl (fun s _ => ldtensor_blockAct_blockEmb K g s (F s))
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.GradedWeylDivisibility
