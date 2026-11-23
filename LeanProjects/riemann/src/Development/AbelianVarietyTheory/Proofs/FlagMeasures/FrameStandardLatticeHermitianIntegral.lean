import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocStdInt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars (Valuation.integer (ValuativeRel.valuation F)))

def hl (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

lemma h_prF (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h (Fr.prF v) y = H.h v y - ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      - ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  show hl H y (Fr.prF v) = _
  simp only [FrameD.prF, map_sub, map_sum, map_smul, smul_eq_mul]
  rfl

lemma h_expand (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h v y = H.h (Fr.prF v) y + ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  rw [h_prF H Fr v y]
  ring

lemma h_prF_es (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v : V) (b : Fin r) :
    H.h (Fr.prF v) (Fr.es b) = 0 := by
  rw [h_prF H Fr v (Fr.es b)]
  have hdual : ∀ a, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun a => Fr.h_es a b
  simp [hdual, Fr.h_ss]

lemma h_symm_mem (H : HermSp M V) {x y : V} (h : H.h x y ∈ M.L.O) : H.h y x ∈ M.L.O := by
  rw [H.h_herm]
  exact cj_mem h

lemma span_left (H : HermSp M V) (S : Set V) (y : V) (h : ∀ x ∈ S, H.h x y ∈ M.L.O) :
    ∀ x ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : H.h 0 y = 0 := (hl H y).map_zero
    rw [h0]
    exact zero_mem _
  | add x x' _ _ hx hx' =>
    rw [H.h_add_left]
    exact add_mem hx hx'
  | smul c x _ hx =>
    rw [Subring.smul_def, H.h_smul_left]
    exact mul_mem c.2 hx

private lemma form_mem_O_of_frame_coords_mem_O (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) {u v : V}
    (hu : (∀ a, H.h u (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h u (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF u ∧ H.mkW Fr.f w ∈ L)
    (hv : (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L) :
    H.h u v ∈ M.L.O := by
  obtain ⟨hus, hue, wu, hwu, hwuL⟩ := hu
  obtain ⟨hvs, hve, wv, hwv, hwvL⟩ := hv
  have hpp : H.h (Fr.prF v) (Fr.prF u) ∈ M.L.O := by
    have h0 := (hL.2.1 wv).1 hwvL wu hwuL
    rwa [hwv, hwu] at h0
  have hwu0 : ∀ x ∈ H.X Fr.f, H.h (wu : V) x = 0 := wu.2
  have he0 : ∀ a, H.h (Fr.e a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, ← hwu, hwu0 (Fr.e a) (Submodule.subset_span ⟨a, rfl⟩), map_zero]
  have hs0 : ∀ a, H.h (Fr.es a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, h_prF_es H Fr u a, map_zero]
  have hvu : H.h v (Fr.prF u) ∈ M.L.O := by
    rw [h_expand H Fr v (Fr.prF u)]
    simp only [he0, hs0, mul_zero, Finset.sum_const_zero, add_zero]
    exact hpp
  rw [h_expand H Fr u v]
  refine add_mem (add_mem (h_symm_mem H hvu) ?_) ?_
  · exact sum_mem fun a _ => mul_mem (hus a) (h_symm_mem H (hve a))
  · exact sum_mem fun a _ => mul_mem (hue a) (h_symm_mem H (hvs a))

theorem lamStd_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L), ∀ x ∈ Fr.LamStd L, ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr L hL x hx y hy
  unfold FrameD.LamStd at hx hy
  refine span_left H _ y ?_ x hx
  intro u hu
  exact h_symm_mem H (span_left H _ u (fun v hv => form_mem_O_of_frame_coords_mem_O H Fr L hL hv hu) y hy)

end GlobalTheory.LocStdInt
