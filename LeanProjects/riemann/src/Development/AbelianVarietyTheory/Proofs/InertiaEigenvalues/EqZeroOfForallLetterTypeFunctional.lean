import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

noncomputable section

open Polynomial Module

namespace GlobalTheory.LetterSep

theorem eq_zero_of_forall_letterHom {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D]
    (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F]
    [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L]
    [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D]
    (hm : ∀ (c : U) (x : D), c • x = m c x)
    (hk : ∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) (x : D)
    (hx : ∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F),
      f x = 0) :
    x = 0 := by
  classical
  let sm : L → D →ₗ[U] D := fun a =>
    { toFun := fun x => a • x, map_add' := smul_add a
      map_smul' := fun c x => by rw [hm, RingHom.id_apply, hm, map_smul] }
  let r : L →+* Module.End F (D →ₗ[U] F) :=
    { toFun := fun a =>
        { toFun := fun f => f ∘ₗ sm a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp [sm]
      map_mul' := fun a b => by ext f x; simp [sm, smul_smul, mul_comm]
      map_zero' := by ext f x; simp [sm]
      map_add' := fun a b => by ext f x; simp [sm, add_smul] }
  have hr : ∀ a f y, r a f y = f (a • y) := fun _ _ _ => rfl
  have hrk : ∀ c : k, r (algebraMap k L c) =
      algebraMap F (Module.End F (D →ₗ[U] F)) (algebraMap k F c) := fun c => by
    ext f y
    rw [hr, ← hk, ← hm, map_smul, Module.algebraMap_end_apply, LinearMap.smul_apply, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply, smul_eq_mul]
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hpoly : ∀ a : L, ∃ q : k[X], a = aeval α q := fun a => by
    have : a ∈ (IntermediateField.adjoin k {α}).toSubalgebra := by rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at this
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq.symm⟩
  have hev : ∀ q : k[X], r (aeval α q) = aeval (r α) (q.map (algebraMap k F)) := fun q => by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    exact RingHom.ext hrk
  have hE : ∀ s : L →ₐ[k] F, (⨅ a, (r a).eigenspace (s a)) = (r α).eigenspace (s α) := fun s => by
    refine le_antisymm (iInf_le _ α) (le_iInf fun a y hy => ?_)
    obtain ⟨q, rfl⟩ := hpoly a
    rw [End.mem_eigenspace_iff] at hy ⊢
    rw [hev, End.aeval_apply_of_mem_apply_eq_smul hy, eval_map_algebraMap, aeval_algHom_apply]
  have h0 : aeval (r α) ((minpoly k α).map (algebraMap k F)) = 0 := by
    rw [← hev, minpoly.aeval, map_zero]
  have hss : (r α).IsSemisimple := End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k α)).squarefree h0
  have htop : ⊤ ≤ ⨆ s : L →ₐ[k] F, ⨅ a, (r a).eigenspace (s a) := by
    rw [← hss.iSup_eigenspace_eq_top]
    refine iSup_le fun μ y hy => ?_
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_mem _
    have h1 := End.aeval_apply_of_mem_apply_eq_smul (p := (minpoly k α).map (algebraMap k F))
      (End.mem_eigenspace_iff.mp hy)
    rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero_iff_left hy0, eval_map_algebraMap] at h1
    have h2 : μ ∈ Set.range fun s : L →ₐ[k] F => s α := by
      rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly F α, mem_rootSet]
      exact ⟨minpoly.ne_zero hint, h1⟩
    obtain ⟨s, rfl⟩ := h2
    exact Submodule.mem_iSup_of_mem s (by rw [hE s]; exact hy)
  by_contra hx0
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual U D, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff U x).mp h)
  let f : D →ₗ[U] F := (Algebra.linearMap U F) ∘ₗ φ
  have hf : f x ≠ 0 := by
    simp only [f, LinearMap.comp_apply, Algebra.linearMap_apply]
    exact (_root_.map_ne_zero _).mpr hφ
  apply hf
  refine Submodule.iSup_induction (motive := fun g : D →ₗ[U] F => g x = 0) _ (htop (Submodule.mem_top (x := f)))
    (fun s g hg => ?_) rfl (fun g h hg hh => by simp [hg, hh])
  have h1 : ∀ a y, g (a • y) = s a * g y := by
    intro a y
    have := (Submodule.mem_iInf _).mp hg a
    rw [End.mem_eigenspace_iff] at this
    have := LinearMap.congr_fun this y
    simpa [hr] using this
  have h2 : ∀ c y, g (m c y) = algebraMap U F c * g y := by
    intro c y
    rw [← hm, g.map_smul, Algebra.smul_def]
  exact hx s g.toAddMonoidHom ⟨h1, h2⟩

end GlobalTheory.LetterSep
