import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec

noncomputable section

namespace PI.LevelKSplit.W.NCL

open PI.VolSemiDirect.W.PG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

def pV (D : Dat A n r) : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

private theorem hL_apply_lemma (D : Dat A n r) (x y : n → A) : D.hL x y = D.h x y := rfl

private theorem pX_apply_lemma_2 (D : Dat A n r) (x : n → A) :
    D.pX x = ∑ a, D.h (D.f a) x • D.e a := by
  simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma]

private theorem pXv_apply_lemma_3 (D : Dat A n r) (x : n → A) :
    D.pXv x = ∑ a, D.h (D.e a) x • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma]

private theorem h_add_lemma_4 (D : Dat A n r) (v x y : n → A) : D.h v (x + y) = D.h v x + D.h v y :=
  map_add (D.hL v) x y

private theorem h_sub_lemma_5 (D : Dat A n r) (v x y : n → A) : D.h v (x - y) = D.h v x - D.h v y :=
  map_sub (D.hL v) x y

private theorem h_sum_lemma_6 (D : Dat A n r) (v : n → A) (t : Fin r → A) (w : Fin r → n → A) :
    D.h v (∑ a, t a • w a) = ∑ a, t a * D.h v (w a) := by
  rw [← hL_apply_lemma, map_sum]
  simp only [map_smul, smul_eq_mul, hL_apply_lemma]

private theorem h_swap_lemma_7 (D : Dat A n r) (H : D.Hyp) (x y : n → A) :
    D.h y x = D.σA (D.h x y) := by
  show (∑ i, ∑ j, D.σA (y i) * D.JA i j * x j) = D.σA (∑ i, ∑ j, D.σA (x i) * D.JA i j * y j)
  simp only [map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem h_fe_lemma_8 (D : Dat A n r) (H : D.Hyp) (a b : Fin r) :
    D.h (D.f a) (D.e b) = if b = a then 1 else 0 := by
  rw [h_swap_lemma_7 D H, H.ef]
  split_ifs <;> simp

private theorem h_add_left_lemma_9 (D : Dat A n r) (H : D.Hyp) (x x' y : n → A) :
    D.h (x + x') y = D.h x y + D.h x' y := by
  rw [h_swap_lemma_7 D H, h_add_lemma_4, map_add, ← h_swap_lemma_7 D H, ← h_swap_lemma_7 D H]

private theorem h_sum_left_lemma_10 (D : Dat A n r) (H : D.Hyp) (t : Fin r → A) (w : Fin r → n → A)
    (y : n → A) : D.h (∑ a, t a • w a) y = ∑ a, D.σA (t a) * D.h (w a) y := by
  rw [h_swap_lemma_7 D H, h_sum_lemma_6, map_sum]
  simp only [map_mul, ← h_swap_lemma_7 D H]

theorem pV_apply (D : Dat A n r) (x : n → A) : pV D x = x - D.pX x - D.pXv x := rfl

theorem decomp (D : Dat A n r) (x : n → A) : x = pV D x + D.pX x + D.pXv x := by
  rw [pV_apply]
  abel

def levL (D : Dat A n r) (U W : Matrix (Fin r) (Fin r) A) : (n → A) →ₗ[A] (n → A) :=
  pV D + ∑ a, ∑ b, U a b • (D.hL (D.f b)).smulRight (D.e a) +
    ∑ d, ∑ b, W d b • (D.hL (D.e b)).smulRight (D.f d)

theorem levL_apply (D : Dat A n r) (U W : Matrix (Fin r) (Fin r) A) (x : n → A) :
    levL D U W x = pV D x + ∑ a, (∑ b, U a b * D.h (D.f b) x) • D.e a +
      ∑ d, (∑ b, W d b * D.h (D.e b) x) • D.f d := by
  simp only [levL, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, hL_apply_lemma, Finset.sum_smul, smul_smul]

variable {D : Dat A n r}

section Hyp

variable (H : D.Hyp)
include H

theorem h_f_pX (c : Fin r) (x : n → A) : D.h (D.f c) (D.pX x) = D.h (D.f c) x := by
  rw [pX_apply_lemma_2, h_sum_lemma_6]
  simp [h_fe_lemma_8 D H]

theorem h_f_pXv (c : Fin r) (x : n → A) : D.h (D.f c) (D.pXv x) = 0 := by
  rw [pXv_apply_lemma_3, h_sum_lemma_6]
  simp [H.ff]

theorem h_e_pX' (c : Fin r) (x : n → A) : D.h (D.e c) (D.pX x) = 0 := by
  rw [pX_apply_lemma_2, h_sum_lemma_6]
  simp [H.ee]

theorem h_e_pXv (c : Fin r) (x : n → A) : D.h (D.e c) (D.pXv x) = D.h (D.e c) x := by
  rw [pXv_apply_lemma_3, h_sum_lemma_6]
  simp [H.ef]

theorem h_f_pV (c : Fin r) (x : n → A) : D.h (D.f c) (pV D x) = 0 := by
  rw [pV_apply, h_sub_lemma_5, h_sub_lemma_5, h_f_pX H, h_f_pXv H]
  ring

theorem h_e_pV (c : Fin r) (x : n → A) : D.h (D.e c) (pV D x) = 0 := by
  rw [pV_apply, h_sub_lemma_5, h_sub_lemma_5, h_e_pX' H, h_e_pXv H]
  ring

theorem h_f_levL (U W : Matrix (Fin r) (Fin r) A) (c : Fin r) (x : n → A) :
    D.h (D.f c) (levL D U W x) = ∑ b, U c b * D.h (D.f b) x := by
  rw [levL_apply, h_add_lemma_4, h_add_lemma_4, h_f_pV H, h_sum_lemma_6, h_sum_lemma_6]
  simp [h_fe_lemma_8 D H, H.ff]

theorem h_e_levL (U W : Matrix (Fin r) (Fin r) A) (c : Fin r) (x : n → A) :
    D.h (D.e c) (levL D U W x) = ∑ b, W c b * D.h (D.e b) x := by
  rw [levL_apply, h_add_lemma_4, h_add_lemma_4, h_e_pV H, h_sum_lemma_6, h_sum_lemma_6]
  simp [H.ee, H.ef]

theorem pV_levL (U W : Matrix (Fin r) (Fin r) A) (x : n → A) :
    pV D (levL D U W x) = pV D x := by
  rw [pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp only [h_f_levL H, h_e_levL H]
  rw [levL_apply]
  abel

theorem ext_coord {y y' : n → A} (h1 : pV D y = pV D y')
    (h2 : ∀ c, D.h (D.f c) y = D.h (D.f c) y') (h3 : ∀ c, D.h (D.e c) y = D.h (D.e c) y') :
    y = y' := by
  rw [decomp D y, decomp D y', h1, pX_apply_lemma_2, pX_apply_lemma_2, pXv_apply_lemma_3, pXv_apply_lemma_3]
  simp only [h2, h3]

theorem levL_comp (U W U' W' : Matrix (Fin r) (Fin r) A) (x : n → A) :
    levL D U W (levL D U' W' x) = levL D (U * U') (W * W') x := by
  apply ext_coord H
  · rw [pV_levL H, pV_levL H, pV_levL H]
  · intro c
    simp only [h_f_levL H, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  · intro c
    simp only [h_e_levL H, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

theorem levL_one (x : n → A) : levL D 1 1 x = x := by
  apply ext_coord H
  · exact pV_levL H 1 1 x
  · intro c
    rw [h_f_levL H]
    simp [Matrix.one_apply]
  · intro c
    rw [h_e_levL H]
    simp [Matrix.one_apply]

theorem levL_e (U W : Matrix (Fin r) (Fin r) A) (b : Fin r) :
    levL D U W (D.e b) = ∑ a, U a b • D.e a := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [h_fe_lemma_8 D H, H.ee]

theorem levL_f (U W : Matrix (Fin r) (Fin r) A) (b : Fin r) :
    levL D U W (D.f b) = ∑ d, W d b • D.f d := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [H.ff, H.ef]

theorem levL_alt (U W : Matrix (Fin r) (Fin r) A) {w : n → A} (hf : ∀ b, D.h (D.f b) w = 0)
    (he : ∀ b, D.h (D.e b) w = 0) : levL D U W w = w := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [hf, he]

theorem levL_sub_perp (U W : Matrix (Fin r) (Fin r) A) {v : n → A} (he : ∀ b, D.h (D.e b) v = 0) :
    levL D U W v - v ∈ Submodule.span A (Set.range D.e) := by
  have key : levL D U W v - v =
      ∑ a, (∑ b, U a b * D.h (D.f b) v) • D.e a - ∑ a, D.h (D.f a) v • D.e a := by
    rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
    simp only [he, mul_zero, Finset.sum_const_zero, zero_smul, sub_zero, add_zero]
    abel
  rw [key]
  exact Submodule.sub_mem _
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

private theorem h_pV_e_lemma_11 (x : n → A) (a : Fin r) : D.h (pV D x) (D.e a) = 0 := by
  rw [h_swap_lemma_7 D H, h_e_pV H, map_zero]

private theorem h_pV_f_lemma_12 (x : n → A) (a : Fin r) : D.h (pV D x) (D.f a) = 0 := by
  rw [h_swap_lemma_7 D H, h_f_pV H, map_zero]

theorem h_decomp (x y : n → A) :
    D.h x y = D.h (pV D x) (pV D y) + ∑ a, D.σA (D.h (D.f a) x) * D.h (D.e a) y +
      ∑ a, D.σA (D.h (D.e a) x) * D.h (D.f a) y := by
  have hx : D.h x y = D.h (pV D x) y + D.h (D.pX x) y + D.h (D.pXv x) y := by
    conv_lhs => rw [decomp D x]
    rw [h_add_left_lemma_9 D H, h_add_left_lemma_9 D H]
  have hy : D.h (pV D x) y = D.h (pV D x) (pV D y) := by
    conv_lhs => rw [decomp D y]
    rw [h_add_lemma_4, h_add_lemma_4, pX_apply_lemma_2, pXv_apply_lemma_3, h_sum_lemma_6, h_sum_lemma_6]
    simp [h_pV_e_lemma_11 H, h_pV_f_lemma_12 H]
  rw [hx, hy, pX_apply_lemma_2, pXv_apply_lemma_3, h_sum_left_lemma_10 D H, h_sum_left_lemma_10 D H]

end Hyp

theorem sum_conj (σ : A →+* A) (U W : Fin r → Fin r → A) (α β : Fin r → A)
    (h : ∀ b c, ∑ a, σ (U a b) * W a c = if b = c then 1 else 0) :
    ∑ a, σ (∑ b, U a b * α b) * ∑ c, W a c * β c = ∑ b, σ (α b) * β b := by
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ c, ∑ a, ∑ b, σ (U a b) * σ (α b) * (W a c * β c)
      = ∑ c, ∑ b, (∑ a, σ (U a b) * W a c) * (σ (α b) * β c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ b, σ (α b) * β b := by
        rw [Finset.sum_comm]
        simp [h]

theorem levL_uni (H : D.Hyp) (U W : Matrix (Fin r) (Fin r) A)
    (hUW : ∀ b c, ∑ a, D.σA (U a b) * W a c = if b = c then 1 else 0)
    (hWU : ∀ b c, ∑ a, D.σA (W a b) * U a c = if b = c then 1 else 0) (x y : n → A) :
    D.h (levL D U W x) (levL D U W y) = D.h x y := by
  rw [h_decomp H (levL D U W x), h_decomp H x y, pV_levL H, pV_levL H]
  simp only [h_f_levL H, h_e_levL H]
  rw [sum_conj D.σA U W _ _ hUW, sum_conj D.σA W U _ _ hWU]

end PI.LevelKSplit.W.NCL
