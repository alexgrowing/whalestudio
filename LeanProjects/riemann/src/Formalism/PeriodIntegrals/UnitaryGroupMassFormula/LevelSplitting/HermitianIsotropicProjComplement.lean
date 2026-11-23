import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemiGen

noncomputable section

namespace PI.LevelKSplit.W.SemiG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

def FixEZ (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z

def Uni (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := ∀ x y, D.h (S x) (S y) = D.h x y

def MapX (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop :=
  ∀ a, S (D.e a) ∈ Submodule.span A (Set.range D.e)

def MapW (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop :=
  ∀ w, IsW D w → (∀ b, D.h (D.e b) (S w) = 0) ∧ D.h D.z (S w) = 0

variable {D : Dat A n r}

private theorem hL_apply_lemma (x y : n → A) : D.hL x y = D.h x y := rfl

theorem h_e_pX (H : D.Hyp) (b : Fin r) (u : n → A) : D.h (D.e b) (D.pX u) = 0 := by
  rw [← hL_apply_lemma]
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
  simp only [hL_apply_lemma, H.ee, smul_zero, Finset.sum_const_zero]

private theorem D_h_sum_left {ι : Type} (s : Finset ι) (g : ι → n → A) (y : n → A) :
    D.h (∑ a ∈ s, g a) y = ∑ a ∈ s, D.h (g a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Dat.h, hform]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_left, ih]

theorem h_pX_left {y : n → A} (hy : ∀ b, D.h (D.e b) y = 0) (u : n → A) : D.h (D.pX u) y = 0 := by
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply, D_h_sum_left, h_smul_left, hy, mul_zero,
    Finset.sum_const_zero]

theorem h_pX_right (H : D.Hyp) {y : n → A} (hy : ∀ b, D.h (D.e b) y = 0) (u : n → A) :
    D.h y (D.pX u) = 0 := by
  rw [h_symm H (D.pX u) y, h_pX_left hy, map_zero]

theorem h_span_left {x y : n → A} (hx : x ∈ Submodule.span A (Set.range D.e))
    (hy : ∀ b, D.h (D.e b) y = 0) : D.h x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hy a
  | zero => simp [Dat.h, hform]
  | add x x' _ _ h1 h2 => rw [h_add_left, h1, h2, add_zero]
  | smul c x _ h1 => rw [h_smul_left, h1, mul_zero]

theorem pW_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) :
    D.pW x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact pW_e H a
  | zero => exact map_zero _
  | add x x' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
  | smul c x _ h1 => rw [map_smul, h1, smul_zero]

theorem pX_mem_span (u : n → A) : D.pX u ∈ Submodule.span A (Set.range D.e) := by
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem S_span {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : S x ∈ Submodule.span A (Set.range D.e) := by
  have hle : Submodule.span A (Set.range D.e) ≤ (Submodule.span A (Set.range D.e)).comap S :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hX a)
  exact hle hx

theorem pW_S_pX (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (u : n → A) :
    D.pW (S (D.pX u)) = 0 :=
  pW_span H (S_span hX (pX_mem_span u))

theorem isotropic_proj_image_complement {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) {w : n → A} (hw : IsW D w) :
    D.pU (S w) = D.pX (S w) := by
  simp only [pU, LinearMap.add_apply, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, hL_apply_lemma, (hW w hw).1, (hW w hw).2, smul_eq_mul, mul_zero, zero_smul,
    Finset.sum_const_zero, add_zero]

theorem complement_proj_image {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) {w : n → A} (hw : IsW D w) :
    D.pW (S w) = S w - D.pX (S w) := by
  simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
  rw [isotropic_proj_image_complement hW hw]

theorem Pi_comp (H : D.Hyp) {S S' : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (hW' : D.MapW S')
    (v : n → A) : D.Pi S (D.Pi S' v) = D.Pi (S ∘ₗ S') v := by
  have hw := isW_pW H v
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, map_add, pU_pU H, pU_pW H, pW_pU H, pW_pW H,
    map_zero, add_zero, zero_add]
  rw [complement_proj_image hW' hw, map_sub, map_sub, pW_S_pX H hX, sub_zero]

theorem Pi_e (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) (a : Fin r) : D.Pi S (D.e a) = D.e a := by
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, pU_e H, pW_e H, map_zero, add_zero]

theorem Pi_f (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) (a : Fin r) : D.Pi S (D.f a) = D.f a := by
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, pU_f H, pW_f H, map_zero, add_zero]

theorem unipotent_proj_fixes_normal (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) : D.Pi S D.z = D.z := by
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, pU_z_eq H, orthogonal_proj_normal_zero H, map_zero, add_zero]

theorem hermitian_isotropic_proj_complement (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h (D.pU x) w = 0 := by
  simp only [pU, LinearMap.add_apply, pX, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, h_add_left, D_h_sum_left, h_smul_left, hw.1, hw.2.1, hw.2.2, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem h_W_pU (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h w (D.pU x) = 0 := by
  rw [h_symm H (D.pU x) w, hermitian_isotropic_proj_complement H hw, map_zero]

theorem h_dec (H : D.Hyp) (x y : n → A) :
    D.h x y = D.h (D.pU x) (D.pU y) + D.h (D.pW x) (D.pW y) := by
  have ex : x = D.pU x + D.pW x := by simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]; abel
  have ey : y = D.pU y + D.pW y := by simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]; abel
  conv_lhs => rw [ex, ey]
  rw [h_add_left, h_add_right, h_add_right, hermitian_isotropic_proj_complement H (isW_pW H y), h_W_pU H (isW_pW H x)]
  simp

private theorem D_h_sub_left (a b c : n → A) : D.h (a - b) c = D.h a c - D.h b c := by
  rw [sub_eq_add_neg, ← neg_one_smul A b, h_add_left, h_smul_left, map_neg, map_one, neg_one_mul,
    ← sub_eq_add_neg]

private theorem D_h_sub_right (a b c : n → A) : D.h c (a - b) = D.h c a - D.h c b := by
  rw [sub_eq_add_neg, ← neg_one_smul A b, h_add_right, h_smul_right, neg_one_mul, ← sub_eq_add_neg]

theorem Pi_uni (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) (hU : D.Uni S) :
    D.Uni (D.Pi S) := by
  intro x y
  have key : ∀ w w', IsW D w → IsW D w' → D.h (D.pW (S w)) (D.pW (S w')) = D.h w w' := by
    intro w w' hw hw'
    rw [complement_proj_image hW hw, complement_proj_image hW hw', D_h_sub_left, D_h_sub_right, D_h_sub_right,
      h_pX_left (hW w' hw').1, h_pX_right H (hW w hw).1, h_pX_left (fun b => h_e_pX H b (S w')), hU]
    simp
  have hPU : ∀ v, D.pU (D.Pi S v) = D.pU v := fun v => by
    simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, map_add, pU_pU H, pU_pW H, add_zero]
  have hPW : ∀ v, D.pW (D.Pi S v) = D.pW (S (D.pW v)) := fun v => by
    simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, map_add, pW_pU H, pW_pW H, zero_add]
  rw [h_dec H, hPU, hPU, hPW, hPW, key _ _ (isW_pW H x) (isW_pW H y), ← h_dec H]

theorem h_e_S {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r)
    (w : n → A) : D.h (D.e b) (S w) = D.h (D.e b) w := by
  rw [← hU (D.e b) w, hS.1 b]

theorem h_z_S {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (w : n → A) :
    D.h D.z (S w) = D.h D.z w := by
  rw [← hU D.z w, hS.2]

theorem Pi_of_fix (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hf : ∀ a, S (D.f a) = D.f a) (hU : D.Uni S) (v : n → A) : D.Pi S v = S v := by
  have hSU : S (D.pU v) = D.pU v := by
    simp only [pU, LinearMap.add_apply, pX, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
      map_add, map_sum, map_smul, hS.1, hf, hS.2]
  have hw := isW_pW H v
  have h1 : ∀ a, D.h (D.e a) (S (D.pW v)) = 0 := fun a => by rw [h_e_S hS hU, hw.1]
  have h2 : ∀ a, D.h (D.f a) (S (D.pW v)) = 0 := fun a => by rw [← hf a, hU, hw.2.1]
  have h3 : D.h D.z (S (D.pW v)) = 0 := by rw [h_z_S hS hU, hw.2.2]
  have hpUS : D.pU (S (D.pW v)) = 0 := by
    simp only [pU, LinearMap.add_apply, pX, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, hL_apply_lemma, h1, h2, h3, smul_eq_mul, mul_zero, zero_smul,
      Finset.sum_const_zero, add_zero]
  have hpW : D.pW (S (D.pW v)) = S (D.pW v) := by
    rw [show D.pW (S (D.pW v)) = S (D.pW v) - D.pU (S (D.pW v)) from rfl, hpUS, sub_zero]
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, hpW]
  rw [← hSU, ← map_add]
  congr 1
  simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
  abel

theorem Pi_of_N (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)}
    (hN : ∀ v, (∀ a, D.h (D.e a) v = 0) → S v - v ∈ Submodule.span A (Set.range D.e))
    (v : n → A) : D.Pi S v = v := by
  have hw := isW_pW H v
  have h1 := pW_span H (hN _ hw.1)
  rw [map_sub, pW_pW H, sub_eq_zero] at h1
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, h1]
  simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
  abel

theorem mapW_of_inv {S Si : (n → A) →ₗ[A] (n → A)} (hSSi : ∀ v, S (Si v) = v) (hU : D.Uni S)
    (hXi : D.MapX Si) (hZi : Si D.z - D.z ∈ Submodule.span A (Set.range D.e)) : D.MapW S := by
  intro w hw
  refine ⟨fun b => ?_, ?_⟩
  · rw [← hSSi (D.e b), hU]
    exact h_span_left (hXi b) hw.1
  · rw [← hSSi D.z, hU]
    have hz : Si D.z = D.z + (Si D.z - D.z) := by abel
    rw [hz, h_add_left, hw.2.2, h_span_left hZi hw.1, add_zero]

theorem N_part (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (hW : D.MapW S)
    (hZ : S D.z - D.z ∈ Submodule.span A (Set.range D.e)) (v : n → A)
    (hv : ∀ a, D.h (D.e a) v = 0) : S v - D.Pi S v ∈ Submodule.span A (Set.range D.e) := by
  have hw := isW_pW H v
  have hpXv : D.pXv v = 0 := by
    simp only [pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma, hv, zero_smul,
      Finset.sum_const_zero]
  have hdec : D.pU v = D.pX v + D.pz v := by
    simp only [pU, LinearMap.add_apply, hpXv, add_zero]
  have hpz : S (D.pz v) - D.pz v ∈ Submodule.span A (Set.range D.e) := by
    simp only [pz, LinearMap.smulRight_apply, map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ hZ
  have hSv : S v = S (D.pU v) + S (D.pW v) := by
    rw [← map_add]
    congr 1
    simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have e1 : S v - D.Pi S v =
      (S (D.pX v) - D.pX v) + (S (D.pz v) - D.pz v) + D.pX (S (D.pW v)) := by
    simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply]
    rw [complement_proj_image hW hw, hSv, hdec, map_add]
    abel
  rw [e1]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ (S_span hX (pX_mem_span v)) (pX_mem_span v)) hpz) (pX_mem_span _)

end Dat

end PI.LevelKSplit.W.SemiG
