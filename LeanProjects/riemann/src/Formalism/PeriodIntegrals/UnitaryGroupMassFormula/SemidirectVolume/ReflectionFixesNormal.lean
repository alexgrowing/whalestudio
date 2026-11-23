import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable {D : Dat A n r}

theorem L_e (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) (a : Fin r) :
    D.L w s (D.e a) = D.e a := by
  have hz0 : ∀ x, D.h x 0 = 0 := fun x => by simpa using h_smul_right (D := D) x 0 0
  simp [L_apply, pW_e H, H.ee, hz0]

theorem reflection_fixes_normal (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) : D.L w s D.z = D.z := by
  have hz0 : ∀ x, D.h x 0 = 0 := fun x => by simpa using h_smul_right (D := D) x 0 0
  simp [L_apply, orthogonal_proj_normal_zero H, H.ez, hz0]

theorem L_f (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) (b : Fin r) :
    D.L w s (D.f b) = D.f b + (w b + ∑ a, s a b • D.e a) := by
  have hz0 : ∀ x, D.h x 0 = 0 := fun x => by simpa using h_smul_right (D := D) x 0 0
  simp [L_apply, pW_f H, H.ef, hz0, Finset.sum_add_distrib]

theorem L_fixEZ (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) : D.FixEZ (D.L w s) := by
  show (∀ a, _ = _) ∧ _ = _
  exact ⟨fun a => L_e H w s a, reflection_fixes_normal H w s⟩

theorem L_perp (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) : D.PerpX (D.L w s) := by
  intro v hv
  rw [L_apply]
  simp only [hv, zero_smul, Finset.sum_const_zero, add_zero]
  rw [sub_sub_cancel_left]
  exact Submodule.neg_mem _
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem coordW_L (H : D.Hyp) {w : Fin r → n → A} (hw : ∀ a, IsW D (w a)) (s : Fin r → Fin r → A)
    (b : Fin r) : D.pW (D.L w s (D.f b)) = w b := by
  rw [L_f H]
  simp [pW_f H, pW_of_isW (hw b), pW_e H]

theorem coordS_L (H : D.Hyp) {w : Fin r → n → A} (hw : ∀ a, IsW D (w a)) (s : Fin r → Fin r → A)
    (a b : Fin r) : D.h (D.f a) (D.L w s (D.f b)) = s a b := by
  have key : ∀ a', D.h (D.f a) (D.e a') = if a' = a then 1 else 0 := by
    intro a'
    rw [h_symm H, H.ef]
    split_ifs <;> simp
  have hwb : (∀ c, D.h (D.e c) (w b) = 0) ∧ (∀ c, D.h (D.f c) (w b) = 0) ∧ D.h D.z (w b) = 0 :=
    hw b
  rw [L_f H]
  simp [h_add_right, h_sum_right, h_smul_right, H.ff, hwb.2.1 a, key]

theorem N_eq_L (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S)
    (hP : D.PerpX S) (v : n → A) :
    S v = D.L (fun b => D.pW (S (D.f b))) (fun a b => D.h (D.f a) (S (D.f b))) v := by
  have hS' : (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z := hS
  set T := D.L (fun b => D.pW (S (D.f b))) (fun a b => D.h (D.f a) (S (D.f b))) with hT
  have he : ∀ a, S (D.e a) = T (D.e a) := fun a => by rw [hS'.1 a, L_e H]
  have hz : S D.z = T D.z := by rw [hS'.2, reflection_fixes_normal H]
  have hf : ∀ b, S (D.f b) = T (D.f b) := fun b => by
    rw [L_f H]; exact (N_f H hS hU b).trans (add_assoc _ _ _)
  have hw : ∀ u, IsW D u → S u = T u := by
    intro u hu
    have hu' : (∀ a, D.h (D.e a) u = 0) ∧ (∀ a, D.h (D.f a) u = 0) ∧ D.h D.z u = 0 := hu
    have hdiff : S u - u ∈ Submodule.span A (Set.range D.e) := hP u hu'.1
    have hpw : D.pW (S u) = u := by
      have h1 : D.pW (S u - u) = 0 := pW_span H hdiff
      rw [map_sub, pW_of_isW hu] at h1
      exact sub_eq_zero.mp h1
    have hSu : S u = u + D.pX (S u) := by
      have h2 := complement_proj_image hS hU hu
      rw [hpw] at h2
      exact sub_eq_iff_eq_add.mp h2.symm
    have hcoef : ∀ a, D.h (D.f a) (S u) = - D.h (D.pW (S (D.f a))) u := by
      intro a
      have h0 : D.h (S (D.f a)) (S u) = 0 := by rw [hU (D.f a) u]; exact hu'.2.1 a
      rw [N_f H hS hU a, ← pX_apply, h_add_left, h_add_left] at h0
      have hX : D.h (D.pX (S (D.f a))) (S u) = 0 :=
        h_pX_left (fun c => by rw [h_e_S hS hU]; exact hu'.1 c) _
      have hW : D.h (D.pW (S (D.f a))) (S u) = D.h (D.pW (S (D.f a))) u := by
        have h3 : S u = u + (S u - u) := by abel
        rw [h3, h_add_right, h_W_span H (isW_pW H _) hdiff, add_zero]
      rw [hX, hW, add_zero] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hTu : T u = u - ∑ a, D.h (D.pW (S (D.f a))) u • D.e a := by
      rw [hT, L_apply, pW_of_isW hu]
      simp [hu'.1]
    rw [hTu, hSu, pX_apply]
    simp only [hcoef, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  have key : v = D.pX v + D.pXv v + D.pz v + D.pW v := by
    rw [pW_apply, pU_apply]; abel
  have h1 : S (D.pX v) = T (D.pX v) := by
    rw [pX_apply]; simp only [map_sum, map_smul, he]
  have h2 : S (D.pXv v) = T (D.pXv v) := by
    rw [pXv_apply]; simp only [map_sum, map_smul, hf]
  have h3 : S (D.pz v) = T (D.pz v) := by
    rw [pz_apply, map_smul, map_smul, hz]
  have h4 : S (D.pW v) = T (D.pW v) := hw _ (isW_pW H v)
  rw [key]
  simp only [map_add, h1, h2, h3, h4]

theorem h_f_pX (H : D.Hyp) (a : Fin r) (u : n → A) : D.h (D.f a) (D.pX u) = D.h (D.f a) u := by
  have key : ∀ a', D.h (D.f a) (D.e a') = if a' = a then 1 else 0 := by
    intro a'
    rw [h_symm H, H.ef]
    split_ifs <;> simp
  rw [pX_apply, h_sum_right]
  simp [h_smul_right, key]

theorem h_pX_f (H : D.Hyp) (b : Fin r) (u : n → A) :
    D.h (D.pX u) (D.f b) = D.σA (D.h (D.f b) u) := by
  rw [pX_apply, h_sum_left]
  simp [h_smul_left, H.ef]

theorem h_W_f (H : D.Hyp) {w : n → A} (hw : IsW D w) (b : Fin r) : D.h w (D.f b) = 0 := by
  have hw' : (∀ c, D.h (D.e c) w = 0) ∧ (∀ c, D.h (D.f c) w = 0) ∧ D.h D.z w = 0 := hw
  rw [h_symm H, hw'.2.1 b, map_zero]

theorem N_f' (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r) :
    S (D.f b) = D.f b + D.pW (S (D.f b)) + D.pX (S (D.f b)) := by
  rw [pX_apply]
  exact N_f H hS hU b

theorem N_skew (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (a b : Fin r) :
    D.h (D.f a) (S (D.f b)) + D.σA (D.h (D.f b) (S (D.f a))) +
      D.h (D.pW (S (D.f a))) (D.pW (S (D.f b))) = 0 := by
  have h0 : D.h (S (D.f a)) (S (D.f b)) = 0 := by rw [hU (D.f a) (D.f b)]; exact H.ff a b
  have hWa := isW_pW H (S (D.f a))
  have hWb : (∀ c, D.h (D.e c) (D.pW (S (D.f b))) = 0) ∧
      (∀ c, D.h (D.f c) (D.pW (S (D.f b))) = 0) ∧ D.h D.z (D.pW (S (D.f b))) = 0 :=
    isW_pW H _
  rw [N_f' H hS hU a, N_f' H hS hU b] at h0
  simp only [h_add_left, h_add_right] at h0
  rw [H.ff a b, hWb.2.1 a, h_f_pX H a, h_W_f H hWa b,
    h_W_span H hWa (pX_mem_span (S (D.f b))), h_pX_f H b, h_pX_left hWb.1,
    h_pX_left (fun c => h_e_pX H c (S (D.f b)))] at h0
  linear_combination h0

theorem pW_comm (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hf : ∀ a, S (D.f a) = D.f a) (hU : D.Uni S) (v : n → A) : D.pW (S v) = S (D.pW v) := by
  have hS' : (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z := hS
  have hfix : ∀ x, S (D.pU x) = D.pU x := by
    intro x
    rw [pU_apply, pX_apply, pXv_apply, pz_apply]
    simp only [map_add, map_sum, map_smul, hS'.1, hf, hS'.2]
  have hwW : ∀ u, IsW D u → D.pW (S u) = S u := by
    intro u hu
    have hu' : (∀ a, D.h (D.e a) u = 0) ∧ (∀ a, D.h (D.f a) u = 0) ∧ D.h D.z u = 0 := hu
    have h0 : ∀ a, D.h (D.f a) (S u) = 0 := fun a => by
      rw [← hf a, hU (D.f a) u]; exact hu'.2.1 a
    rw [complement_proj_image hS hU hu, pX_apply]
    simp [h0]
  have hv : v = D.pU v + D.pW v := by rw [pW_apply]; abel
  conv_lhs => rw [hv]
  rw [map_add, map_add, hfix, pW_pU H, zero_add, hwW _ (isW_pW H v)]

end Dat

end PI.VolSemiDirect.W.PG
