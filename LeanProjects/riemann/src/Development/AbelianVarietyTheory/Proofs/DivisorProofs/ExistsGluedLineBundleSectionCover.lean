import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

namespace GlobalTheory.GlueOver

open GlobalTheory.KS

variable {X : Scheme.{0}}

theorem rsT_cocycle {M : LB X} (hM : M.IsLB) (a b c : M.ι) {O : X.Opens} (h : O ≤ M.U a ⊓ M.U b ⊓ M.U c) :
    rsT (M.g a b).val O * rsT (M.g b c).val O = rsT (M.g a c).val O := by
  have e := congrArg (fun u => rsT u.val O) (hM.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, rsT_mul] at e
  rwa [rsT_rsT inf_le_left h, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem rsT_g_self {M : LB X} (hM : M.IsLB) (a : M.ι) {O : X.Opens} (h : O ≤ M.U a) :
    rsT (M.g a a).val O = 1 := by
  have h2 : O ≤ M.U a ⊓ M.U a := le_inf h h
  have e := rsT_cocycle hM a a a (le_inf h2 h)
  have hu : IsUnit (rsT (M.g a a).val O) := by
    rw [rsT_of_le h2]
    exact (M.g a a).isUnit.map _
  exact hu.mul_left_cancel (e.trans (_root_.mul_one _).symm)

theorem exists_glue : ∀ {X : Scheme.{0}} (M : LB X), M.IsLB → ∀ (V : X.Opens) {J : Type} (W : J → X.Opens)
    (j : J → M.ι) (F : ∀ i, Γ(X, W i)), ⨆ i, W i = V → (∀ i, W i ≤ M.U (j i)) →
    (∀ i i', rsT (F i) (W i ⊓ W i') = rsT (M.g (j i) (j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i')) →
    ∃ t : ∀ c, Γ(X, M.U c ⊓ V),
      (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ V) =
        rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ V) * rsT (t c') (M.U c ⊓ M.U c' ⊓ V)) ∧
      ∀ i, rsT (t (j i)) (W i) = F i := by
  intro X M hM V J W j F hV hW Fc
  have hWV : ∀ i, W i ≤ V := fun i => hV ▸ le_iSup W i
  have cov : ∀ O : X.Opens, O ⊓ V ≤ ⨆ i, O ⊓ W i := by
    intro O y hy
    have : y ∈ ⨆ i, W i := by rw [hV]; exact hy.2
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy.1, hi⟩
  have hU : ∀ c i, M.U c ⊓ W i ≤ M.U c ⊓ M.U (j i) := fun c i => inf_le_inf le_rfl (hW i)
  have hUV : ∀ (O : X.Opens) i, O ⊓ W i ≤ O ⊓ V := fun O i => inf_le_inf le_rfl (hWV i)
  have glue : ∀ c : M.ι, ∃ t : Γ(X, M.U c ⊓ V), ∀ i,
      rsT t (M.U c ⊓ W i) = rsT (M.g c (j i)).val (M.U c ⊓ W i) * rsT (F i) (M.U c ⊓ W i) := by
    intro c
    refine exists_rsT_eq (fun i => M.U c ⊓ W i) (fun i => hUV _ i) (cov _) _ fun i i' => ?_
    have hN1 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i := inf_le_left
    have hN2 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i' := inf_le_right
    have hNW : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ W i ⊓ W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have h3 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ M.U (j i) ⊓ M.U (j i') :=
      fun y hy => ⟨⟨hy.1.1, hW i hy.1.2⟩, hW i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_rsT (hU c i) hN1, rsT_rsT (hU c i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_rsT (inf_le_inf (hW i) (hW i')) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  choose t ht using glue
  refine ⟨t, fun c c' => ?_, fun i => ?_⟩
  · refine eq_of_rsT_eq (fun i => M.U c ⊓ M.U c' ⊓ W i) (fun i => hUV _ i) (cov _) _ _ fun i => ?_
    have a1 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c' ⊓ W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have h3 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ M.U (j i) := inf_le_inf le_rfl (hW i)
    have e' : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ V := hUV _ i
    have eL : M.U c ⊓ M.U c' ⊓ V ≤ M.U c ⊓ V := fun y hy => ⟨hy.1.1, hy.2⟩
    have eR : M.U c ⊓ M.U c' ⊓ V ≤ M.U c' ⊓ V := fun y hy => ⟨hy.1.2, hy.2⟩
    rw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', rsT_rsT inf_le_left e',
      ← rsT_rsT (hUV _ i) a1 (t c), ← rsT_rsT (hUV _ i) a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_rsT (hU c i) a1, rsT_rsT (hU c' i) a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  · have a : W i ≤ M.U (j i) ⊓ W i := le_inf (hW i) le_rfl
    rw [← rsT_rsT (hUV _ i) a, ht, rsT_mul, rsT_rsT (hU _ i) a, rsT_rsT inf_le_right a, rsT_self,
      rsT_g_self hM (j i) (hW i), _root_.one_mul]

end GlobalTheory.GlueOver
