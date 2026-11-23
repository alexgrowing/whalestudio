import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F V V' : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module F V] [Module ℂ V]
  [IsScalarTower ℂ F V] [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

private lemma actF_tmul (a b : F) (v : V) (v' : V') :
    actF F V V' (a ⊗ₜ b) (v ⊗ₜ v') = (a • v) ⊗ₜ (b • v') := by
  simp [actF, Module.endTensorEndAlgHom_apply]

private noncomputable def Ph (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] F ⊗[ℂ] F :=
  TensorProduct.map (ψ.restrictScalars ℂ) (ψ'.restrictScalars ℂ)

private lemma Ph_tmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (a : V) (b : V') :
    Ph ψ ψ' (a ⊗ₜ b) = ψ a ⊗ₜ ψ' b := rfl

private lemma Ph_act (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (s : F ⊗[ℂ] F) (t : V ⊗[ℂ] V') :
    Ph ψ ψ' (actF F V V' s t) = s * Ph ψ ψ' t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mul, ha, hb]
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add c e hc he => simp only [map_add, mul_add, hc, he]
    | tmul c e => simp [actF_tmul, Ph_tmul]

private lemma Ph_lmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (t : V ⊗[ℂ] V') :
    Algebra.TensorProduct.lmul' ℂ (Ph ψ ψ' t) = ψ' (ctrF V' ψ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add c e hc he => simp only [map_add, hc, he]
  | tmul c e => simp [Ph_tmul, ctrF]

variable {A A' : Subalgebra ℂ F} {M : Submodule ℂ V} {M' : Submodule ℂ V'}

private lemma Ph_mem {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    Ph ψ ψ' t ∈ (Algebra.TensorProduct.map A.val A'.val).range := by
  have key : Submodule.map₂ (TensorProduct.mk ℂ V V') M M' ≤
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range).comap (Ph ψ ψ') := by
    refine Submodule.map₂_le.2 fun m hm m' hm' => ?_
    exact ⟨(⟨ψ m, h m hm⟩ : A) ⊗ₜ (⟨ψ' m', h' m' hm'⟩ : A'), by simp [Ph_tmul]⟩
  exact key ht

private lemma act_mem (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {s : F ⊗[ℂ] F}
    (hs : s ∈ (Algebra.TensorProduct.map A.val A'.val).range) :
    actF F V V' s (v ⊗ₜ v') ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' := by
  obtain ⟨r, rfl⟩ := hs
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, actF_tmul]
    exact Submodule.apply_mem_map₂ _ (hA _ a.2 _ hv) (hA' _ a'.2 _ hv')
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem hx hy

private lemma decomp {n n' : ℕ} {v : Fin n → V} {φ : Fin n → V →ₗ[F] F} {v' : Fin n' → V'}
    {φ' : Fin n' → V' →ₗ[F] F} (h : ∀ m ∈ M, m = ∑ k, φ k m • v k) (h' : ∀ m ∈ M', m = ∑ k, φ' k m • v' k)
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    t = ∑ k, ∑ l, actF F V V' (Ph (φ k) (φ' l) t) (v k ⊗ₜ v' l) := by
  rw [Submodule.map₂_eq_span_image2] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    simp only [TensorProduct.mk_apply, Ph_tmul, actF_tmul]
    conv_lhs => rw [h a ha, h' b hb]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  | zero => simp
  | add a b _ _ ha hb =>
    conv_lhs => rw [ha, hb]
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  | smul c a _ ha =>
    conv_lhs => rw [ha]
    simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum]

private lemma Ph_sm {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {T : Set (F ⊗[ℂ] F)} {t : V ⊗[ℂ] V'}
    (ht : t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T) :
    Ph ψ ψ' t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T := by
  have hle : sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T ≤
      (sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
        (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T).comap (Ph ψ ψ') := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap, Ph_act]
    exact Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr ⟨_, Ph_mem h h' hu, by simp⟩)
  exact hle ht

private lemma act_sm (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {T : Set (F ⊗[ℂ] F)} {s : F ⊗[ℂ] F}
    (hs : s ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T) :
    actF F V V' s (v ⊗ₜ v') ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
  let L : (F ⊗[ℂ] F) →ₗ[ℂ] V ⊗[ℂ] V' :=
    (LinearMap.applyₗ (v ⊗ₜ v')) ∘ₗ (actF F V V').toLinearMap
  have hle : sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T ≤
      (sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T).comap L := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr
      ⟨actF F V V' u (v ⊗ₜ v'), act_mem hA hA' hv hv' hu, ?_⟩)
    simp [L, Module.End.mul_apply]
  exact hle hs

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.regLat_of :
    Reg0 → Ker0 → RegLat := by
  intro h0 hK F _ _ d x hx V V' _ _ _ _ _ _ _ _ I J M M' hL hL' j hjI hjJ
  obtain ⟨hA, n, v, φ, hv, hφ, hdec⟩ := hL
  obtain ⟨hA', n', v', φ', hv', hφ', hdec'⟩ := hL'
  have back : ∀ (T : Set (F ⊗[ℂ] F)) (t : V ⊗[ℂ] V'), t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' →
      (∀ k l, Ph (φ k) (φ' l) t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) T) →
      t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
    intro T t ht h
    rw [decomp hdec hdec' ht]
    exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
      act_sm hA hA' (hv k) (hv' l) (h k l)
  refine ⟨?_, ?_⟩
  · intro k m hm hk
    refine back _ m hm fun a b => ?_
    refine h0 F d x hx I J j hjI hjJ k _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    have := Ph_sm (ψ := φ a) (ψ' := φ' b) (fun m hm => hφ a m hm) (fun m hm => hφ' b m hm) hk
    rw [Ph_act] at this
    exact this
  · intro m hm hψ
    refine back _ m hm fun a b => ?_
    refine hK F d x hx I J j hjI hjJ _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    rw [Ph_lmul, hψ, map_zero]
