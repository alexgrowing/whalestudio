import Formalism.LatticeTheta.Statement

noncomputable section

namespace Formalism.H

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma dualLattice_innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  first
    | exact (LinearMap.BilinForm.nondegenerate_iff (innerₗ V)
        (fun x => by rw [innerₗ_apply_apply]; exact real_inner_self_nonneg) isSymm_inner).2
        (fun x => by rw [innerₗ_apply_apply]; exact inner_self_eq_zero)
    | (unfold LinearMap.BilinForm.Nondegenerate
       intro m hm
       have h := hm m
       rw [innerₗ_apply_apply] at h
       exact inner_self_eq_zero.mp h)

lemma innerₗ_isSymm : LinearMap.BilinForm.IsSymm (innerₗ V) := by
  first
    | exact fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _
    | exact ⟨fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _⟩
    | (intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)
    | (constructor; intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)

variable [FiniteDimensional ℝ V]

lemma exists_basis_span_eq (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (e : Module.Basis ι ℝ V),
      Submodule.span ℤ (Set.range e) = Λ := by
  classical
  exact ⟨Module.Free.ChooseBasisIndex ℤ Λ, inferInstance, inferInstance,
    Module.Basis.ofZLatticeBasis ℝ Λ (Module.Free.chooseBasis ℤ Λ),
    Module.Basis.ofZLatticeBasis_span ℝ Λ _⟩

lemma isLattice_of_eq_span {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ V) (L : Submodule ℤ V)
    (h : L = Submodule.span ℤ (Set.range e)) :
    DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
  subst h
  refine ⟨inferInstance, ?_⟩
  intro _
  infer_instance

lemma dualLattice_dual_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) =
      Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ V) dualLattice_innerₗ_nondegenerate e)) := LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) dualLattice_innerₗ_nondegenerate e

end Formalism.H
