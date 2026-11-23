import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

lemma herm_add_left (u u' v : ι → ℂ) : herm H (u + u') v = herm H u v + herm H u' v := by
  simp [herm, Matrix.mulVec_add]
lemma herm_add_right (u v v' : ι → ℂ) : herm H u (v + v') = herm H u v + herm H u v' := by
  simp [herm]
lemma herm_smul_left (c : ℂ) (u v : ι → ℂ) : herm H (c • u) v = c * herm H u v := by
  simp [herm, Matrix.mulVec_smul]
lemma herm_smul_right (c : ℂ) (u v : ι → ℂ) : herm H u (c • v) = conj c * herm H u v := by
  simp [herm] <;> rfl
lemma herm_conj (hH : Hᴴ = H) (u v : ι → ℂ) : conj (herm H u v) = herm H v u := by
  have hc : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [Matrix.conjTranspose_apply] at this
  show star (star v ⬝ᵥ (H *ᵥ u)) = star u ⬝ᵥ (H *ᵥ v)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
lemma tk_herm_conjTranspose [DecidableEq ι] (g : Matrix ι ι ℂ) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm (gᴴ * H * g) u v := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
lemma herm_UH [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  rw [tk_herm_conjTranspose, show gᴴ * H * g = H from hg]
lemma tk_herm_single [DecidableEq ι] (i j : ι) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  simp [herm]
lemma mem_UH_of [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : ∀ u v, herm H (g *ᵥ u) (g *ᵥ v) = herm H u v) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  rw [← tk_herm_single (gᴴ * H * g) i j, ← tk_herm_conjTranspose, hg, tk_herm_single]
end herm

def mk3 (k r' : ℕ) (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  a • e0 k r' + liftVec k 1 r' y + b • es0 k r'

def cF (u : Fin (2 * (1 + r') + k + 1) → ℂ) : ℂ := u ⟨0, by omega⟩

def cL (u : Fin (2 * (1 + r') + k + 1) → ℂ) : ℂ := u ⟨2 * (1 + r') + k, by omega⟩

def mid (u : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => u (levPos k 1 r' j)

private lemma e0_apply_eq_ite (i : Fin (2 * (1 + r') + k + 1)) : e0 k r' i = if i.val = 0 then 1 else 0 := by
  have h : (i = eI k (1 + r') (a0 r')) ↔ i.val = 0 := Fin.ext_iff
  simp only [e0, bvec, Pi.single_apply, h]

private lemma es0_apply (i : Fin (2 * (1 + r') + k + 1)) :
    es0 k r' i = if i.val = 2 * (1 + r') + k then 1 else 0 := by
  have h : (i = esI k (1 + r') (a0 r')) ↔ i.val = 2 * (1 + r') + k := Fin.ext_iff
  simp only [es0, bvec, Pi.single_apply, h]

lemma three_block_apply (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) (i : Fin (2 * (1 + r') + k + 1)) :
    mk3 k r' a y b i = if i.val = 0 then a else if h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1 then y ⟨i.val - 1, by omega⟩ else b := by
  have hi := i.isLt
  simp only [mk3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e0_apply_eq_ite, es0_apply, liftVec]
  split_ifs <;> first | omega | simp

lemma three_block_first (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) : cF (mk3 k r' a y b) = a := by
  simp only [cF, three_block_apply, Fin.val_mk]
  split_ifs <;> first | rfl | omega
lemma three_block_last (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) : cL (mk3 k r' a y b) = b := by
  simp only [cL, three_block_apply, Fin.val_mk]
  split_ifs <;> first | rfl | omega
lemma three_block_middle (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) : mid (mk3 k r' a y b) = y := by
  funext j
  have hj := j.isLt
  show mk3 k r' a y b (levPos k 1 r' j) = y j
  rw [three_block_apply]
  have c1 : ¬ ((levPos k 1 r' j).val = 0) := by simp only [levPos, Fin.val_mk]; omega
  have c2 : 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 := by
    simp only [levPos, Fin.val_mk]; omega
  rw [if_neg c1, dif_pos c2]
  exact congrArg y (Fin.ext (by simp only [levPos, Fin.val_mk]; omega))
lemma three_block_eta (u : Fin (2 * (1 + r') + k + 1) → ℂ) : mk3 k r' (cF u) (mid u) (cL u) = u := by
  funext i
  have hi := i.isLt
  rw [three_block_apply]
  split_ifs with h1 h2
  · exact congrArg u (Fin.ext (by (try simp only [Fin.val_mk]); omega))
  · exact congrArg u (Fin.ext (by (try simp only [levPos, Fin.val_mk]); omega))
  · exact congrArg u (Fin.ext (by (try simp only [Fin.val_mk]); omega))
lemma three_block_injective {a a' b b' : ℂ} {y y' : Fin (2 * r' + k + 1) → ℂ} (h : mk3 k r' a y b = mk3 k r' a' y' b') :
    a = a' ∧ y = y' ∧ b = b' := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg cF h; rwa [three_block_first, three_block_first] at this
  · have := congrArg mid h; rwa [three_block_middle, three_block_middle] at this
  · have := congrArg cL h; rwa [three_block_last, three_block_last] at this
lemma e0_eq : e0 k r' = mk3 k r' 1 0 0 := by
  funext i
  have hi := i.isLt
  rw [e0_apply_eq_ite, three_block_apply]
  split_ifs <;> first | omega | simp
lemma dual_base_vector_eq_single : es0 k r' = mk3 k r' 0 0 1 := by
  funext i
  have hi := i.isLt
  rw [es0_apply, three_block_apply]
  split_ifs <;> first | omega | simp
lemma lift_eq (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y = mk3 k r' 0 y 0 := by
  funext i
  have hi := i.isLt
  rw [three_block_apply]
  simp only [liftVec]
  split_ifs <;> first | omega | simp
lemma three_block_add (a a' b b' : ℂ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    mk3 k r' a y b + mk3 k r' a' y' b' = mk3 k r' (a + a') (y + y') (b + b') := by
  funext i
  simp only [Pi.add_apply, three_block_apply]
  split_ifs <;> simp
lemma three_block_smul (c a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    c • mk3 k r' a y b = mk3 k r' (c * a) (c • y) (c * b) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, three_block_apply]
  split_ifs <;> simp
lemma three_block_sub (a a' b b' : ℂ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    mk3 k r' a y b - mk3 k r' a' y' b' = mk3 k r' (a - a') (y - y') (b - b') := by
  funext i
  simp only [Pi.sub_apply, three_block_apply]
  split_ifs <;> simp

lemma sum_split_first_middle_last {N n : ℕ} (h : N = n + 2) (f : Fin N → ℂ) :
    ∑ i, f i = f ⟨0, by omega⟩ + ∑ j : Fin n, f ⟨j.val + 1, by omega⟩ + f ⟨n + 1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, ← add_assoc]
  rfl

def tkF (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def tkL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

lemma tk_sum (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ i, f i = f (tkF k r') + ∑ j, f (levPos k 1 r' j) + f (tkL k r') := by
  rw [sum_split_first_middle_last (n := 2 * r' + k + 1) (by omega) f]
  have h : (⟨2 * r' + k + 1 + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = tkL k r' :=
    Fin.ext (by simp only [tkL, Fin.val_mk]; omega)
  rw [h]
  try rfl

lemma tk_mulVec (A : Mat k (1 + r')) (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * (1 + r') + k + 1)) :
    (A *ᵥ mk3 k r' a y b) i = A i (tkF k r') * a + ∑ j, A i (levPos k 1 r' j) * y j + A i (tkL k r') * b := by
  simp only [Matrix.mulVec, dotProduct]
  rw [tk_sum]
  have h1 : mk3 k r' a y b (tkF k r') = a := three_block_first a y b
  have h2 : ∀ j, mk3 k r' a y b (levPos k 1 r' j) = y j := fun j => congrFun (three_block_middle a y b) j
  have h3 : mk3 k r' a y b (tkL k r') = b := three_block_last a y b
  simp only [h1, h2, h3]

lemma three_block_ext {u v : Fin (2 * (1 + r') + k + 1) → ℂ} (h1 : u (tkF k r') = v (tkF k r'))
    (h2 : ∀ j, u (levPos k 1 r' j) = v (levPos k 1 r' j)) (h3 : u (tkL k r') = v (tkL k r')) : u = v := by
  calc u = mk3 k r' (cF u) (mid u) (cL u) := (three_block_eta u).symm
    _ = mk3 k r' (cF v) (mid v) (cL v) := by
      rw [show cF u = cF v from h1, show mid u = mid v from funext h2, show cL u = cL v from h3]
    _ = v := three_block_eta v

lemma eq_three_block_of_coordinates {u : Fin (2 * (1 + r') + k + 1) → ℂ} {a b : ℂ} {y : Fin (2 * r' + k + 1) → ℂ}
    (h1 : u (tkF k r') = a) (h2 : ∀ j, u (levPos k 1 r' j) = y j) (h3 : u (tkL k r') = b) : u = mk3 k r' a y b := by
  apply three_block_ext
  · rw [h1]; exact (three_block_first a y b).symm
  · intro j; rw [h2]; exact (congrFun (three_block_middle a y b) j).symm
  · rw [h3]; exact (three_block_last a y b).symm

lemma hermitian_matrix_three_block (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ mk3 k r' a y b = mk3 k r' b (Hpk k r' *ᵥ y) a := by
  apply eq_three_block_of_coordinates
  · rw [tk_mulVec]
    have h1 : Hpk k (1 + r') (tkF k r') (tkF k r') = 0 := by
      unfold Hpk tkF
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h2 : ∀ j, Hpk k (1 + r') (tkF k r') (levPos k 1 r' j) = 0 := by
      intro j; have := j.isLt
      unfold Hpk tkF levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h3 : Hpk k (1 + r') (tkF k r') (tkL k r') = 1 := by
      unfold Hpk tkF tkL
      dsimp only
      rw [if_pos (by omega)]
    simp [h1, h2, h3]
  · intro i
    have hi := i.isLt
    rw [tk_mulVec]
    have h1 : Hpk k (1 + r') (levPos k 1 r' i) (tkF k r') = 0 := by
      unfold Hpk tkF levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; dsimp only; omega)]
    have h2 : ∀ j, Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
      intro j; have := j.isLt
      unfold Hpk levPos
      dsimp only
      have c1 : (i.val + 1 < 1 + r' ∧ i.val + 1 + (j.val + 1) = 2 * (1 + r') + k) ↔ (i.val < r' ∧ i.val + j.val = 2 * r' + k) := by omega
      have c2 : (j.val + 1 < 1 + r' ∧ i.val + 1 + (j.val + 1) = 2 * (1 + r') + k) ↔ (j.val < r' ∧ i.val + j.val = 2 * r' + k) := by omega
      have c3 : (1 + r' ≤ i.val + 1 ∧ i.val + 1 ≤ 1 + r' + k ∧
          (⟨i.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = ⟨j.val + 1, by omega⟩) ↔ (r' ≤ i.val ∧ i.val ≤ r' + k ∧ i = j) := by
        rw [Fin.ext_iff, Fin.ext_iff]; dsimp only; omega
      have c4 : (i.val + 1 = 1 + r' + k) ↔ (i.val = r' + k) := by omega
      simp only [c1, c2, c3, c4]
    have h3 : Hpk k (1 + r') (levPos k 1 r' i) (tkL k r') = 0 := by
      unfold Hpk tkL levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; dsimp only; omega)]
    simp [h1, h2, h3, Matrix.mulVec, dotProduct]
  · rw [tk_mulVec]
    have h1 : Hpk k (1 + r') (tkL k r') (tkF k r') = 1 := by
      unfold Hpk tkF tkL
      dsimp only
      rw [if_neg (by omega), if_pos (by omega)]
    have h2 : ∀ j, Hpk k (1 + r') (tkL k r') (levPos k 1 r' j) = 0 := by
      intro j; have := j.isLt
      unfold Hpk tkL levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h3 : Hpk k (1 + r') (tkL k r') (tkL k r') = 0 := by
      unfold Hpk tkL
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [h1, h2, h3]

lemma hermitian_three_block (a a' b b' : ℂ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (mk3 k r' a y b) (mk3 k r' a' y' b') =
      a * conj b' + b * conj a' + herm (Hpk k r') y y' := by
  unfold herm
  rw [hermitian_matrix_three_block]
  simp only [dotProduct, Pi.star_apply]
  rw [tk_sum]
  have e1 : ∀ (a : ℂ) y (b : ℂ), mk3 k r' a y b (tkF k r') = a := fun a y b => three_block_first a y b
  have e2 : ∀ (a : ℂ) y (b : ℂ) j, mk3 k r' a y b (levPos k 1 r' j) = y j :=
    fun a y b j => congrFun (three_block_middle a y b) j
  have e3 : ∀ (a : ℂ) y (b : ℂ), mk3 k r' a y b (tkL k r') = b := fun a y b => three_block_last a y b
  simp only [e1, e2, e3, starRingEnd_apply]
  ring

lemma matrix_ext_three_block {A B : Mat k (1 + r')} (h : ∀ a y b, A *ᵥ mk3 k r' a y b = B *ᵥ mk3 k r' a y b) : A = B := by
  have h' : ∀ u, A *ᵥ u = B *ᵥ u := fun u => by rw [← three_block_eta u]; exact h _ _ _
  ext i j
  have := congrFun (h' (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

lemma Hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp
lemma Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
lemma Hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, Hpk_sq, Matrix.det_one]
  exact isUnit_iff_ne_zero.mpr (fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h)

lemma herm_self_im (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) : (herm (Hpk k r) y y).im = 0 := (Complex.conj_eq_iff_im).mp (herm_conj (Hpk k r) (Hpk_herm k r) y y)
open scoped ComplexOrder in

lemma herm_nondeg (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (h : ∀ x, herm (Hpk k r) x y = 0) : y = 0 := by
  have h1 : star y ᵥ* Hpk k r = 0 := by
    funext j
    have := h (Pi.single j 1)
    simp only [herm] at this
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  have h2 : star y = 0 := by
    have := congrArg (fun v => v ᵥ* Hpk k r) h1
    simp only [Matrix.vecMul_vecMul, Hpk_sq, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    exact this
  simpa using congrArg star h2

lemma hb_re (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : (hb k r' y s).re = -(herm (Hpk k r') y y).re / 2 := by
  simp [hb]
lemma hb_im (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : (hb k r' y s).im = s := by
  simp [hb]
lemma hb_add_conj (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + conj (hb k r' y s) = - herm (Hpk k r') y y := by
  apply Complex.ext
  · rw [Complex.add_re, Complex.conj_re, hb_re, Complex.neg_re]; ring
  · rw [Complex.add_im, Complex.conj_im, hb_im, Complex.neg_im, herm_self_im]; ring

lemma eq_hb {y : Fin (2 * r' + k + 1) → ℂ} {b : ℂ} (h : b + conj b = - herm (Hpk k r') y y) : b = hb k r' y b.im := by
  have hr := congrArg Complex.re h
  rw [Complex.add_re, Complex.conj_re, Complex.neg_re] at hr
  apply Complex.ext
  · rw [hb_re]; linarith
  · rw [hb_im]

private lemma ιLev_apply_tkF (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (tkF k r') q = if q.val = 0 then 1 else 0 := by
  have hq := q.isLt
  simp only [ιLev, tkF, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

private lemma ιLev_apply_tkL (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (tkL k r') q = if q.val = 2 * (1 + r') + k then 1 else 0 := by
  have hq := q.isLt
  simp only [ιLev, tkL, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

private lemma ιLev_levPos_apply (g : Mat k r') (i : Fin (2 * r' + k + 1)) (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) q =
      if h : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1 then g i ⟨q.val - 1, by omega⟩ else 0 := by
  have hi := i.isLt
  have hq := q.isLt
  have c1 : 1 ≤ i.val + 1 ∧ i.val + 1 < 2 * r' + k + 1 + 1 := by omega
  simp only [ιLev, levPos, Fin.val_mk, c1, and_self, ↓reduceDIte]
  by_cases hc : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hc, dif_pos hc]
    exact congrFun (congrArg g (Fin.ext (by simp only [Fin.val_mk]; omega))) _
  · rw [dif_neg hc, dif_neg hc]

private lemma ιLev_levPos_levPos (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  have hj := j.isLt
  have c : 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 := by
    simp only [levPos, Fin.val_mk]; omega
  rw [ιLev_levPos_apply, dif_pos c]
  exact congrArg (g i) (Fin.ext (by simp only [levPos, Fin.val_mk]; omega))

private lemma ιLev_levPos_tkF_eq_zero (g : Mat k r') (i : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (tkF k r') = 0 := by
  have c : ¬ (1 ≤ (tkF k r').val ∧ (tkF k r').val < 2 * r' + k + 1 + 1) := by simp only [tkF, Fin.val_mk]; omega
  rw [ιLev_levPos_apply, dif_neg c]

private lemma ιLev_levPos_tkL_eq_zero (g : Mat k r') (i : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (tkL k r') = 0 := by
  have c : ¬ (1 ≤ (tkL k r').val ∧ (tkL k r').val < 2 * r' + k + 1 + 1) := by simp only [tkL, Fin.val_mk]; omega
  rw [ιLev_levPos_apply, dif_neg c]

lemma levi_three_block (g₁ : Mat k r') (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g₁ *ᵥ mk3 k r' a y b = mk3 k r' a (g₁ *ᵥ y) b := by
  have hN0 : 2 * (1 + r') + k ≠ 0 := by omega
  have hN0' : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN : ∀ j : Fin (2 * r' + k + 1), j.val + 1 ≠ 2 * (1 + r') + k := fun j => by have := j.isLt; omega
  have hN' : ∀ j : Fin (2 * r' + k + 1), 2 * (1 + r') + k ≠ j.val + 1 := fun j => by have := j.isLt; omega
  have hL : ¬ (2 * (1 + r') + k < 2 * r' + k + 1 + 1) := by omega
  apply eq_three_block_of_coordinates
  · rw [tk_mulVec]
    simp only [ιLev_apply_tkF]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0]
  · intro j
    rw [tk_mulVec, ιLev_levPos_tkF_eq_zero, ιLev_levPos_tkL_eq_zero]
    simp only [ιLev_levPos_levPos, zero_mul, zero_add, add_zero]
    rfl
  · rw [tk_mulVec]
    simp only [ιLev_apply_tkL]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0', hN]
private lemma w0_tkF_apply_eq_ite_star_inv (c : ℂ) (q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c (tkF k r') q = if q.val = 2 * (1 + r') + k then (star c)⁻¹ else 0 := by
  have hN0 : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN0' : 2 * (1 + r') + k ≠ 0 := by omega
  by_cases h : q.val = 2 * (1 + r') + k
  · simp [w0, tkF, h]
  · simp [w0, tkF, h, hN0, hN0']

private lemma w0_tkL_apply_eq_ite (c : ℂ) (q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c (tkL k r') q = if q.val = 0 then c else 0 := by
  have hN0 : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN0' : 2 * (1 + r') + k ≠ 0 := by omega
  by_cases h : q.val = 0
  · simp [w0, tkL, h, hN0, hN0']
  · simp [w0, tkL, h, hN0, hN0']

private lemma w0_levPos_apply_eq_ite_succ (c : ℂ) (i : Fin (2 * r' + k + 1)) (q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c (levPos k 1 r' i) q = if q.val = i.val + 1 then 1 else 0 := by
  have hi := i.isLt
  have hlt : i.val + 1 < 2 * (1 + r') + k := by omega
  have hne : i.val + 1 ≠ 2 * (1 + r') + k := by omega
  have hv : (levPos k 1 r' i).val = i.val + 1 := rfl
  have hq' : (levPos k 1 r' i = q) ↔ (q.val = i.val + 1) :=
    ⟨fun e => by rw [← e]; rfl, fun e => Fin.ext (by rw [hv, e])⟩
  by_cases h : q.val = i.val + 1
  · simp [w0, hv, hq', h, hlt, hne]
  · simp [w0, hv, hq', h, hlt, hne]

lemma long_weyl_three_block (c a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    w0 k r' c *ᵥ mk3 k r' a y b = mk3 k r' ((conj c)⁻¹ * b) y (c * a) := by
  have hN0 : 2 * (1 + r') + k ≠ 0 := by omega
  have hN0' : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN : ∀ j : Fin (2 * r' + k + 1), j.val + 1 ≠ 2 * (1 + r') + k := fun j => by have := j.isLt; omega
  have hN' : ∀ j : Fin (2 * r' + k + 1), 2 * (1 + r') + k ≠ j.val + 1 := fun j => by have := j.isLt; omega
  have hL : ¬ (2 * (1 + r') + k < 2 * r' + k + 1 + 1) := by omega
  apply eq_three_block_of_coordinates
  · rw [tk_mulVec]
    simp only [w0_tkF_apply_eq_ite_star_inv]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0', hN] <;> rfl
  · intro j
    rw [tk_mulVec]
    simp only [w0_levPos_apply_eq_ite_succ]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN', Fin.val_inj]
  · rw [tk_mulVec]
    simp only [w0_tkL_apply_eq_ite]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0]

lemma tk_herm_sum {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v : Fin m → ℂ) :
    ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma tk_heisAct (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' v b *ᵥ u = u - herm (Hpk k (1 + r')) u v • e0 k r' + herm (Hpk k (1 + r')) u (e0 k r') • (v + b • e0 k r') := by
  simp only [heisG, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  have key : ∀ (w f : Fin (2 * (1 + r') + k + 1) → ℂ), Matrix.vecMulVec w f *ᵥ u = (∑ j, f j * u j) • w := by
    intro w f
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [key, key, tk_herm_sum, tk_herm_sum]

lemma heisenberg_three_block (x : HPar k r') (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ mk3 k r' a y b =
      mk3 k r' (a - herm (Hpk k r') y x.1 + b * hb k r' x.1 x.2) (y + b • x.1) b := by
  have h0 : herm (Hpk k r') y 0 = 0 := by simp [herm]
  unfold heis0
  rw [tk_heisAct, lift_eq, e0_eq, hermitian_three_block, hermitian_three_block]
  simp only [map_zero, map_one, mul_zero, mul_one, zero_add, add_zero, h0, three_block_smul, three_block_add, three_block_sub]
  congr 1 <;> first | ring1 | simp

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def μx : Measure ℂ := (volume : Measure ℂ).withDensity fun c => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹)

instance : SFinite μx := by unfold μx; infer_instance

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem map_mulVec_volume {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (Fin n → ℂ)).map (fun y => A *ᵥ y) = ENNReal.ofReal ((‖A.det‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det ((Matrix.toLin' A).restrictScalars ℝ) = ‖A.det‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hpos : (0 : ℝ) < ‖A.det‖ ^ 2 := by have := norm_pos_iff.2 hA; positivity
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ))
    (f := (Matrix.toLin' A).restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.2 hpos)] at h
  exact h

theorem map_smul_volume {n : ℕ} (c : ℂ) (hc : c ≠ 0) :
    (volume : Measure (Fin n → ℂ)).map (fun y => c • y) = ENNReal.ofReal ((‖c‖ ^ (2 * n))⁻¹) • volume := by
  have hA : (c • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0 := by simp [Matrix.det_smul, hc]
  have e : (fun y : Fin n → ℂ => c • y) = fun y => (c • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ y := by
    funext y; ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [e, map_mulVec_volume _ hA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow, ← pow_mul, mul_comm n 2]

theorem map_mul_volume_real (t : ℝ) (ht : t ≠ 0) :
    (volume : Measure ℝ).map (fun s => t * s) = ENNReal.ofReal (|t|⁻¹) • volume := by
  rw [Real.map_volume_mul_left ht, abs_inv]

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def mi2D (l c : ℂ) : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (l * -((conj c) ^ 2)⁻¹)).restrictScalars ℝ).comp
    (Complex.conjCLE : ℂ →L[ℝ] ℂ)

lemma conj_inverse_map_has_fderiv (l c : ℂ) (hc : c ≠ 0) : HasFDerivAt (fun c : ℂ => l / conj c) (mi2D l c) c := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have h1 : HasDerivAt (fun z : ℂ => l * z⁻¹) (l * -((conj c) ^ 2)⁻¹) (conj c) := (hasDerivAt_inv hc').const_mul l
  have h2 : HasFDerivAt (fun z : ℂ => l * z⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (l * -((conj c) ^ 2)⁻¹)).restrictScalars ℝ) (conj c) :=
    h1.hasFDerivAt.restrictScalars ℝ
  have h3 : HasFDerivAt (fun c : ℂ => conj c) (Complex.conjCLE : ℂ →L[ℝ] ℂ) c := Complex.conjCLE.hasFDerivAt
  have h4 := HasFDerivAt.comp c h2 h3
  have he : (fun c : ℂ => l / conj c) = (fun z : ℂ => l * z⁻¹) ∘ (fun c : ℂ => conj c) := by
    funext z; simp [div_eq_mul_inv]
  rw [he]; exact h4

lemma conj_inverse_map_det (l c : ℂ) : (mi2D l c).det = -(‖l‖ ^ 2 * (‖c‖ ^ 4)⁻¹) := by
  unfold mi2D ContinuousLinearMap.det
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  have h1 : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (l * -((conj c) ^ 2)⁻¹) : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) =
      (l * -((conj c) ^ 2)⁻¹) • LinearMap.id := by
    ext; simp
  have h2 : LinearMap.det ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = -1 := Complex.det_conjAe
  rw [h1, h2, LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]
  simp only [norm_mul, norm_neg, norm_inv, norm_pow, RCLike.norm_conj]
  ring

lemma conj_inverse_map_measurable (l : ℂ) : Measurable fun c : ℂ => l / conj c :=
  measurable_const.div Complex.continuous_conj.measurable

lemma conj_inverse_map_image (l : ℂ) (hl : l ≠ 0) : (fun c : ℂ => l / conj c) '' {(0 : ℂ)}ᶜ = {(0 : ℂ)}ᶜ := by
  have hl' : conj l ≠ 0 := (map_ne_zero _).2 hl
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact div_ne_zero hl ((map_ne_zero _).2 hc)
  · intro hx
    have hx' : conj x ≠ 0 := (map_ne_zero _).2 hx
    refine ⟨conj l / conj x, div_ne_zero hl' hx', ?_⟩
    simp only [map_div₀, Complex.conj_conj]
    field_simp

lemma conj_inverse_map_inj_on (l : ℂ) (hl : l ≠ 0) : Set.InjOn (fun c : ℂ => l / conj c) {(0 : ℂ)}ᶜ := by
  intro a ha b hb hab
  have ha' : conj a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : conj b ≠ 0 := (map_ne_zero _).2 hb
  dsimp only at hab
  rw [div_eq_div_iff ha' hb'] at hab
  have := mul_left_cancel₀ hl hab
  exact ((starRingEnd ℂ).injective this).symm

lemma restrict_compl_zero_eq : (volume : Measure ℂ).restrict {(0 : ℂ)}ᶜ = volume := Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton 0))

theorem μx_map_inv (l : ℂ) (hl : l ≠ 0) : μx.map (fun c => l / conj c) = μx := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hw : Measurable fun c : ℂ => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹) := by fun_prop
  rw [lintegral_map hg (conj_inverse_map_measurable l)]
  unfold μx
  have hgl : Measurable fun a : ℂ => g (l / conj a) := hg.comp (conj_inverse_map_measurable l)
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hg, lintegral_withDensity_eq_lintegral_mul _ hw hgl]
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ)
    (s := {(0 : ℂ)}ᶜ) (f := fun c : ℂ => l / conj c) (f' := mi2D l) (MeasurableSet.singleton _).compl
    (fun x hx => (conj_inverse_map_has_fderiv l x hx).hasFDerivWithinAt) (conj_inverse_map_inj_on l hl)
    ((fun c : ℂ => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹)) * g)
  rw [conj_inverse_map_image l hl, restrict_compl_zero_eq] at key
  rw [key]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ c : ℂ, c ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hae] with c hc
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), conj_inverse_map_det, abs_neg]
  congr 2
  have h1 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have h2 : 0 < ‖l‖ := norm_pos_iff.2 hl
  rw [abs_of_nonneg (by positivity), norm_div, RCLike.norm_conj]
  field_simp

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem lintegral_inv_norm_lt_top (R : ℝ) :
    (∫⁻ c in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (‖c‖⁻¹)) < ∞ := by
  rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet, ← Complex.lintegral_comp_polarCoord_symm]
  have hS : MeasurableSet (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hle : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => ENNReal.ofReal (‖c‖⁻¹)) (Complex.polarCoord.symm p) ≤
      (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    intro p hp
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hR : p.1 ≤ R
    · have hm : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R := by
        rw [mem_closedBall_zero_iff, hn]; exact hR
      have hm2 : p ∈ Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi := ⟨⟨hp1, hR⟩, hp.2⟩
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm2, hn, smul_eq_mul,
        ← ENNReal.ofReal_mul hp1.le, mul_inv_cancel₀ hp1.ne', ENNReal.ofReal_one]
    · have hm : Complex.polarCoord.symm p ∉ Metric.closedBall (0 : ℂ) R := by
        rw [mem_closedBall_zero_iff, hn]; exact hR
      rw [Set.indicator_of_notMem hm, smul_zero]
      exact zero_le
  refine lt_of_le_of_lt (setLIntegral_mono' polarCoord.open_target.measurableSet hle) ?_
  refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
  rw [lintegral_indicator hS, setLIntegral_const, one_mul, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioo]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

def Ψt (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  mk3 k r' (hb k r' p.2.1 p.2.2 / conj p.1) p.2.1 p.1

def Tw (k r' : ℕ) (c₀ : ℂ) (p : ℂ × HPar k r') : ℂ × HPar k r' :=
  (c₀ * hb k r' p.2.1 p.2.2 / conj p.1, (p.2.1, -p.2.2))

def Tl (k r' : ℕ) (g₁ : Mat k r') (p : ℂ × HPar k r') : ℂ × HPar k r' := (p.1, (g₁ *ᵥ p.2.1, p.2.2))

def Tn (k r' : ℕ) (x₀ : HPar k r') (p : ℂ × HPar k r') : ℂ × HPar k r' :=
  (p.1, (p.2.1 + p.1 • x₀.1, p.2.2 - (conj p.1 * herm (Hpk k r') p.2.1 x₀.1).im + ‖p.1‖ ^ 2 * x₀.2))

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

lemma lift_vector_measurable : Measurable (fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y) := by
  rw [measurable_pi_iff]
  intro p
  simp only [liftVec]
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

lemma hermitian_quadratic_continuous : Continuous (fun y : Fin (2 * r' + k + 1) → ℂ => herm (Hpk k r') y y) := by
  unfold herm
  exact continuous_star.dotProduct (continuous_const.matrix_mulVec continuous_id)

lemma heisenberg_coordinate_measurable : Measurable (fun x : HPar k r' => hb k r' x.1 x.2) := by
  have h := hermitian_quadratic_continuous (k := k) (r' := r')
  refine Continuous.measurable ?_
  unfold hb
  exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp (h.comp continuous_fst)).neg.div_const 2)).add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

theorem Ψt_meas : Measurable (Ψt k r') := by
  unfold Ψt mk3
  have h1 : Measurable (fun p : ℂ × HPar k r' => hb k r' p.2.1 p.2.2) := heisenberg_coordinate_measurable.comp measurable_snd
  have h2 : Measurable (fun p : ℂ × HPar k r' => liftVec k 1 r' p.2.1) :=
    lift_vector_measurable.comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable (fun p : ℂ × HPar k r' => conj p.1) := Complex.continuous_conj.measurable.comp measurable_fst
  exact (((h1.div h3).smul_const _).add h2).add (measurable_fst.smul_const _)

lemma unitary_levi_det_norm_one (g₁ : Mat k r') (hg : g₁ ∈ GV k r') : ‖g₁.det‖ = 1 := by
  have hg' : g₁ᴴ * Hpk k r' * g₁ = Hpk k r' := hg
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have hH : (Hpk k r').det ≠ 0 := (Hpk_unit k r').ne_zero
  have h2 : star g₁.det * g₁.det = 1 := by
    have h3 : (star g₁.det * g₁.det - 1) * (Hpk k r').det = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h | h
    · linear_combination h
    · exact absurd h hH
  have h4 : ((‖g₁.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    exact h2
  have h5 : ‖g₁.det‖ ^ 2 = 1 := by exact_mod_cast h4
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5

theorem Tl_mp (g₁ : Mat k r') (hg : g₁ ∈ GV k r') :
    MeasurePreserving (Tl k r' g₁) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by
  have hdet := unitary_levi_det_norm_one g₁ hg
  have hne : g₁.det ≠ 0 := by intro h; rw [h, norm_zero] at hdet; exact zero_ne_one hdet
  have hmv : MeasurePreserving (fun y : Fin (2 * r' + k + 1) → ℂ => g₁ *ᵥ y) volume volume :=
    ⟨(continuous_const.matrix_mulVec continuous_id).measurable, by rw [map_mulVec_volume g₁ hne, hdet]; simp⟩
  exact (MeasurePreserving.id μx).prod (hmv.prod (MeasurePreserving.id (volume : Measure ℝ)))

def cm1Θ (k r' : ℕ) (p : ℂ × HPar k r') : ℂ × HPar k r' := (p.1, (p.1 • p.2.1, ‖p.1‖ ^ 2 * p.2.2))

lemma heisenberg_quadratic_dilation (c : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' (c • y) (‖c‖ ^ 2 * s) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hb k r' y s := by
  unfold hb
  rw [herm_smul_left, herm_smul_right]
  have h : (c * (conj c * herm (Hpk k r') y y)).re = ‖c‖ ^ 2 * (herm (Hpk k r') y y).re := by
    rw [← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  rw [h]
  push_cast
  ring

lemma parametrisation_eq_scaled_sum (p : ℂ × HPar k r') :
    p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r') = Ψt k r' (cm1Θ k r' p) := by
  obtain ⟨c, y, s⟩ := p
  simp only [Ψt, cm1Θ]
  rw [heisenberg_quadratic_dilation, dual_base_vector_eq_single, lift_eq, e0_eq, three_block_smul, three_block_add, three_block_add, three_block_smul]
  by_cases hc : c = 0
  · subst hc; simp
  · have hc' : conj c ≠ 0 := (map_ne_zero _).mpr hc
    have h1 : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
      rw [Complex.mul_conj']; push_cast; rfl
    rw [h1]
    congr 1
    · field_simp
      ring
    · simp
    · simp

lemma heisenberg_dilation_map_measure (c : ℂ) (hc : c ≠ 0) :
    (volume : Measure (HPar k r')).map (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) =
      ENNReal.ofReal ((‖c‖ ^ (2 * (2 * r' + k + 1) + 2))⁻¹) • volume := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have e : (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) =
      Prod.map (fun y : Fin (2 * r' + k + 1) → ℂ => c • y) (fun s : ℝ => ‖c‖ ^ 2 * s) := rfl
  rw [e, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (measurable_const_smul c) (measurable_const_mul _),
    map_smul_volume c hc, map_mul_volume_real _ (by positivity), Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [abs_of_pos (by positivity), ← mul_inv, ← pow_add]

lemma parametrisation_map_measurable : Measurable (cm1Θ k r') := by
  unfold cm1Θ
  fun_prop

lemma parametrisation_map_measure :
    (((volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1)))).prod
      (volume : Measure (HPar k r'))).map (cm1Θ k r') = μx.prod volume := by
  ext s hs
  rw [Measure.map_apply parametrisation_map_measurable hs, Measure.prod_apply (parametrisation_map_measurable hs), Measure.prod_apply hs]
  unfold μx
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_left (parametrisation_map_measurable hs)),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_left hs)]
  apply lintegral_congr
  intro c
  simp only [Pi.mul_apply]
  by_cases hc : c = 0
  · subst hc; simp
  · have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have h1 : Prod.mk c ⁻¹' (cm1Θ k r' ⁻¹' s) =
        (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) ⁻¹' (Prod.mk c ⁻¹' s) := rfl
    have hm : Measurable (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) := by fun_prop
    rw [h1, ← Measure.map_apply hm (measurable_prodMk_left hs), heisenberg_dilation_map_measure c hc, Measure.smul_apply, smul_eq_mul,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [pow_add]
    field_simp

theorem cone_eq : coneMeas k r' = ((μx.prod (volume : Measure (HPar k r')))).map (Ψt k r') := by
  unfold coneMeas
  have e : (fun p : ℂ × HPar k r' => p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')) =
      Ψt k r' ∘ cm1Θ k r' := funext parametrisation_eq_scaled_sum
  rw [e, ← Measure.map_map Ψt_meas parametrisation_map_measurable, parametrisation_map_measure]

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

lemma hermitian_form_continuous {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) :
    Continuous fun p : (ι → ℂ) × (ι → ℂ) => herm H p.1 p.2 := by
  unfold herm
  exact (continuous_star.comp continuous_snd).dotProduct (continuous_const.matrix_mulVec continuous_fst)

lemma heisenberg_quadratic_continuous : Continuous fun q : HPar k r' => hb k r' q.1 q.2 := by
  have h := hermitian_quadratic_continuous (k := k) (r' := r')
  unfold hb
  exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp (h.comp continuous_fst)).neg.div_const 2)).add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

lemma prod_swap_measure_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] : MeasurePreserving Prod.swap (μ.prod ν) (ν.prod μ) := Measure.measurePreserving_swap

lemma ae_second_coordinate_ne_zero : ∀ᵐ q : HPar k r' ∂(volume : Measure (HPar k r')), q.2 ≠ 0 := by
  rw [ae_iff, Measure.volume_eq_prod]
  have : {q : HPar k r' | ¬ q.2 ≠ 0} = Set.univ ×ˢ {0} := by ext q; simp
  rw [this, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem Tw_mp (c₀ : ℂ) (hc : c₀ ≠ 0) :
    MeasurePreserving (Tw k r' c₀) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by
  have hbase : MeasurePreserving (fun q : HPar k r' => ((q.1, -q.2) : HPar k r')) volume volume := by
    have := (MeasurePreserving.id (volume : Measure (Fin (2 * r' + k + 1) → ℂ))).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    rw [← Measure.volume_eq_prod] at this
    exact this
  have hS : MeasurePreserving
      (fun p : HPar k r' × ℂ => (((p.1.1, -p.1.2) : HPar k r'), c₀ * hb k r' p.1.1 p.1.2 / conj p.2))
      ((volume : Measure (HPar k r')).prod μx) ((volume : Measure (HPar k r')).prod μx) := by
    refine hbase.skew_product (g := fun (q : HPar k r') (c : ℂ) => c₀ * hb k r' q.1 q.2 / conj c) ?_ ?_
    · have h1 : Measurable fun p : HPar k r' × ℂ => hb k r' p.1.1 p.1.2 :=
        (heisenberg_quadratic_continuous.comp continuous_fst).measurable
      have h2 : Measurable fun p : HPar k r' × ℂ => conj p.2 :=
        (Complex.continuous_conj.comp continuous_snd).measurable
      exact (h1.const_mul c₀).div h2
    · filter_upwards [ae_second_coordinate_ne_zero] with q hq
      refine μx_map_inv _ (mul_ne_zero hc ?_)
      intro h0
      apply hq
      rw [← hb_im (k := k) (r' := r') q.1 q.2, h0]; rfl
  have hT : Tw k r' c₀ = Prod.swap ∘ (fun p : HPar k r' × ℂ =>
      (((p.1.1, -p.1.2) : HPar k r'), c₀ * hb k r' p.1.1 p.1.2 / conj p.2)) ∘ Prod.swap := by
    funext p; rfl
  rw [hT]
  exact (prod_swap_measure_preserving (volume : Measure (HPar k r')) μx).comp (hS.comp (prod_swap_measure_preserving μx (volume : Measure (HPar k r'))))

theorem Tn_mp (x₀ : HPar k r') :
    MeasurePreserving (Tn k r' x₀) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by
  have hm : Measurable fun p : ℂ × HPar k r' =>
      ((p.2.1 + p.1 • x₀.1, p.2.2 - (conj p.1 * herm (Hpk k r') p.2.1 x₀.1).im + ‖p.1‖ ^ 2 * x₀.2) : HPar k r') := by
    have h : Continuous fun p : ℂ × HPar k r' => herm (Hpk k r') p.2.1 x₀.1 :=
      (hermitian_form_continuous (Hpk k r')).comp ((continuous_fst.comp continuous_snd).prodMk continuous_const)
    have h2 : Continuous fun p : ℂ × HPar k r' => conj p.1 := Complex.continuous_conj.comp continuous_fst
    have h3 : Continuous fun p : ℂ × HPar k r' => (conj p.1 * herm (Hpk k r') p.2.1 x₀.1).im :=
      Complex.continuous_im.comp (h2.mul h)
    apply Continuous.measurable
    fun_prop
  refine (MeasurePreserving.id μx).skew_product
    (g := fun (c : ℂ) (q : HPar k r') => ((q.1 + c • x₀.1, q.2 - (conj c * herm (Hpk k r') q.1 x₀.1).im + ‖c‖ ^ 2 * x₀.2) : HPar k r')) hm ?_
  refine Filter.Eventually.of_forall fun c => ?_
  have hsk : MeasurePreserving
      (fun q : HPar k r' => ((q.1 + c • x₀.1, q.2 - (conj c * herm (Hpk k r') q.1 x₀.1).im + ‖c‖ ^ 2 * x₀.2) : HPar k r'))
      ((volume : Measure (Fin (2 * r' + k + 1) → ℂ)).prod (volume : Measure ℝ))
      ((volume : Measure (Fin (2 * r' + k + 1) → ℂ)).prod (volume : Measure ℝ)) := by
    refine (measurePreserving_add_right (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) (c • x₀.1)).skew_product
      (g := fun (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) => s - (conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2) ?_ ?_
    · exact (hm.comp (measurable_const.prodMk measurable_id : Measurable fun q : HPar k r' => (c, q))).snd
    · refine Filter.Eventually.of_forall fun y => ?_
      have := (measurePreserving_add_right (volume : Measure ℝ)
        (-(conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2)).map_eq
      have he : (fun s : ℝ => s - (conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2) =
          fun s : ℝ => s + (-(conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2) := by
        funext s; ring
      rw [he]; exact this
  exact hsk.map_eq

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

section
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

lemma al_herm_zero_right (u : ι → ℂ) : herm H u 0 = 0 := by
  simp [herm]
lemma al_herm_zero_left (u : ι → ℂ) : herm H 0 u = 0 := by
  simp [herm]
lemma al_herm_neg_left (u v : ι → ℂ) : herm H (-u) v = - herm H u v := by
  simp [herm, Matrix.mulVec_neg]
lemma al_herm_neg_right (u v : ι → ℂ) : herm H u (-v) = - herm H u v := by
  simp [herm]
end

lemma al_inv_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) {v w : Fin n → ℂ} (h : A *ᵥ v = w) :
    A⁻¹ *ᵥ w = v := by
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]

lemma al_one_mem (k r : ℕ) : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp
lemma al_mul_mem {k r : ℕ} {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']
lemma al_unit {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have hH : (Hpk k r).det ≠ 0 := (Hpk_unit k r).ne_zero
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  exact hH h1.symm
lemma al_inv_mem {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  have hu := al_unit hg
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ hu]; simp

lemma al_cL_eq (u : Fin (2 * (1 + r') + k + 1) → ℂ) : herm (Hpk k (1 + r')) u (e0 k r') = cL u := by
  have h := hermitian_three_block (k := k) (r' := r') (cF u) 1 (cL u) 0 (mid u) 0
  rw [three_block_eta, ← e0_eq] at h
  rw [h]
  simp [herm]
lemma al_cF_eq (u : Fin (2 * (1 + r') + k + 1) → ℂ) : herm (Hpk k (1 + r')) u (es0 k r') = cF u := by
  have h := hermitian_three_block (k := k) (r' := r') (cF u) 0 (cL u) 1 (mid u) 0
  rw [three_block_eta, ← dual_base_vector_eq_single] at h
  rw [h]
  simp [herm]

lemma three_block_split (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    mk3 k r' a y b = a • e0 k r' + mk3 k r' 0 y 0 + b • es0 k r' := by
  simp only [mk3, zero_smul, zero_add, add_zero]

lemma heis_mem (x : HPar k r') : heis0 k r' x ∈ GV k (1 + r') := by
  apply mem_UH_of
  intro u v
  rw [← three_block_eta u, ← three_block_eta v, heisenberg_three_block, heisenberg_three_block, hermitian_three_block, hermitian_three_block]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
  have h1 := herm_conj (Hpk k r') (Hpk_herm k r') (mid v) x.1
  have h2 := hb_add_conj (k := k) x.1 x.2
  simp only [map_add, map_sub, map_mul]
  linear_combination (-(cL u)) * h1 + (cL u * (starRingEnd ℂ) (cL v)) * h2

lemma cmHalfIntegralGenerator_mem_algebraicClosure (c : ℂ) (hc : c ≠ 0) : w0 k r' c ∈ GV k (1 + r') := by
  apply mem_UH_of
  intro u v
  rw [← three_block_eta u, ← three_block_eta v, long_weyl_three_block, long_weyl_three_block, hermitian_three_block, hermitian_three_block]
  have hc' : (starRingEnd ℂ) c ≠ 0 := by simpa using hc
  have h1 : ((starRingEnd ℂ) c)⁻¹ * (starRingEnd ℂ) c = 1 := inv_mul_cancel₀ hc'
  have h2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  simp only [map_mul, map_inv₀, Complex.conj_conj]
  linear_combination (cL u * (starRingEnd ℂ) (cF v)) * h1 + (cF u * (starRingEnd ℂ) (cL v)) * h2

lemma lev_mem (g₁ : Mat k r') (hg : g₁ ∈ GV k r') : ιLev k 1 r' g₁ ∈ GV k (1 + r') := by
  apply mem_UH_of
  intro u v
  rw [← three_block_eta u, ← three_block_eta v, levi_three_block, levi_three_block, hermitian_three_block, hermitian_three_block, herm_UH _ hg]

lemma al_hb_neg (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : hb k r' (-y) (-s) = conj (hb k r' y s) := by
  apply Complex.ext
  · rw [Complex.conj_re, hb_re, hb_re, al_herm_neg_left, al_herm_neg_right, neg_neg]
  · rw [Complex.conj_im, hb_im, hb_im]

lemma al_heis_mul_neg (x : HPar k r') : heis0 k r' x * heis0 k r' (-x.1, -x.2) = 1 := by
  apply matrix_ext_three_block
  intro a y b
  rw [← Matrix.mulVec_mulVec, heisenberg_three_block, heisenberg_three_block, Matrix.one_mulVec]
  dsimp only
  congr 1
  · rw [al_hb_neg, al_herm_neg_right, herm_add_left, herm_smul_left, al_herm_neg_left]
    linear_combination b * hb_add_conj x.1 x.2
  · simp

lemma al_heis_inv (x : HPar k r') : (heis0 k r' x)⁻¹ = heis0 k r' (-x.1, -x.2) := Matrix.inv_eq_right_inv (al_heis_mul_neg x)

lemma al_lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply matrix_ext_three_block
  intro a y b
  rw [← Matrix.mulVec_mulVec, levi_three_block, levi_three_block, levi_three_block, Matrix.mulVec_mulVec]

lemma al_lev_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply matrix_ext_three_block
  intro a y b
  rw [levi_three_block, Matrix.one_mulVec, Matrix.one_mulVec]

lemma al_lev_inv {g : Mat k r'} (hg : IsUnit g.det) : (ιLev k 1 r' g)⁻¹ = ιLev k 1 r' g⁻¹ := by
  exact Matrix.inv_eq_right_inv (by rw [← al_lev_mul, Matrix.mul_nonsing_inv _ hg, al_lev_one])

lemma al_mat_ext {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ y, A *ᵥ y = B *ᵥ y) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

lemma heisenberg_fixes_isotropic_vector (x : HPar k r') : heis0 k r' x *ᵥ e0 k r' = e0 k r' := by
  rw [e0_eq, heisenberg_three_block, al_herm_zero_left]
  simp
lemma heisenberg_dual_base_vector (x : HPar k r') : heis0 k r' x *ᵥ es0 k r' = mk3 k r' (hb k r' x.1 x.2) x.1 1 := by
  rw [dual_base_vector_eq_single, heisenberg_three_block, al_herm_zero_left]
  simp
lemma levi_fixes_isotropic_vector (g₁ : Mat k r') : ιLev k 1 r' g₁ *ᵥ e0 k r' = e0 k r' := by
  rw [e0_eq, levi_three_block]
  simp
lemma long_weyl_element_base_vector (c : ℂ) : w0 k r' c *ᵥ e0 k r' = mk3 k r' 0 0 c := by
  rw [e0_eq, long_weyl_three_block]
  simp

def alL (h : Mat k (1 + r')) : (Fin (2 * r' + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r' + k + 1) → ℂ) where
  toFun y := mid (h *ᵥ mk3 k r' 0 y 0)
  map_add' y y' := by
    have : mk3 k r' 0 (y + y') 0 = mk3 k r' 0 y 0 + mk3 k r' 0 y' 0 := by rw [three_block_add]; simp
    rw [this, Matrix.mulVec_add]; rfl
  map_smul' c y := by
    have : mk3 k r' 0 (c • y) 0 = c • mk3 k r' 0 y 0 := by rw [three_block_smul]; simp
    rw [this, Matrix.mulVec_smul]; rfl

lemma al_fix {h : Mat k (1 + r')} (hh : h ∈ GV k (1 + r')) (h1 : h *ᵥ e0 k r' = e0 k r')
    (h2 : h *ᵥ es0 k r' = es0 k r') : ∃ g₁ ∈ GV k r', h = ιLev k 1 r' g₁ := by
  have key : ∀ y, h *ᵥ mk3 k r' 0 y 0 = mk3 k r' 0 (LinearMap.toMatrix' (alL h) *ᵥ y) 0 := by
    intro y
    rw [LinearMap.toMatrix'_mulVec]
    have e1 : cL (h *ᵥ mk3 k r' 0 y 0) = 0 := by
      rw [← al_cL_eq]
      conv_lhs => rw [← h1]
      rw [herm_UH _ hh, al_cL_eq, three_block_last]
    have e2 : cF (h *ᵥ mk3 k r' 0 y 0) = 0 := by
      rw [← al_cF_eq]
      conv_lhs => rw [← h2]
      rw [herm_UH _ hh, al_cF_eq, three_block_first]
    conv_lhs => rw [← three_block_eta (h *ᵥ mk3 k r' 0 y 0), e1, e2]
    rfl
  refine ⟨LinearMap.toMatrix' (alL h), ?_, ?_⟩
  · apply mem_UH_of
    intro y y'
    have := herm_UH _ hh (mk3 k r' 0 y 0) (mk3 k r' 0 y' 0)
    rw [key, key, hermitian_three_block, hermitian_three_block] at this
    simpa using this
  · apply matrix_ext_three_block
    intro a y b
    rw [levi_three_block, three_block_split, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, key,
      ← three_block_split]

theorem al_stabDecomp : StabDecomp := by
  intro k r'
  ext g
  constructor
  · rintro ⟨hg, he⟩
    have hb1 : cL (g *ᵥ es0 k r') = 1 := by
      rw [← al_cL_eq]
      conv_lhs => rw [← he]
      rw [herm_UH _ hg, al_cL_eq, dual_base_vector_eq_single, three_block_last]
    have hq : herm (Hpk k (1 + r')) (g *ᵥ es0 k r') (g *ᵥ es0 k r') = 0 := by
      rw [herm_UH _ hg, al_cF_eq, dual_base_vector_eq_single, three_block_first]
    rw [← three_block_eta (g *ᵥ es0 k r'), hermitian_three_block, hb1] at hq
    have ha : cF (g *ᵥ es0 k r') = hb k r' (mid (g *ᵥ es0 k r')) (cF (g *ᵥ es0 k r')).im := by
      apply eq_hb
      simp only [map_one, mul_one, one_mul] at hq
      linear_combination hq
    set x : HPar k r' := (mid (g *ᵥ es0 k r'), (cF (g *ᵥ es0 k r')).im) with hx
    have hn := heis_mem x
    have hnes : heis0 k r' x *ᵥ es0 k r' = g *ᵥ es0 k r' := by
      rw [heisenberg_dual_base_vector, ← three_block_eta (g *ᵥ es0 k r'), hb1]
      conv_rhs => rw [ha]
    obtain ⟨g₁, hg₁, hgg⟩ := al_fix (h := (heis0 k r' x)⁻¹ * g) (al_mul_mem (al_inv_mem hn) hg)
      (by rw [← Matrix.mulVec_mulVec, he]; exact al_inv_mulVec (al_unit hn) (heisenberg_fixes_isotropic_vector x))
      (by rw [← Matrix.mulVec_mulVec]; exact al_inv_mulVec (al_unit hn) hnes)
    refine ⟨heis0 k r' x, ⟨x, rfl⟩, ιLev k 1 r' g₁, ⟨g₁, hg₁, rfl⟩, ?_⟩
    rw [← hgg, Matrix.mul_nonsing_inv_cancel_left _ _ (al_unit hn)]
  · rintro ⟨n, ⟨x, rfl⟩, l, ⟨g₁, hg₁, rfl⟩, rfl⟩
    refine ⟨al_mul_mem (heis_mem x) (lev_mem g₁ hg₁), ?_⟩
    rw [← Matrix.mulVec_mulVec, levi_fixes_isotropic_vector, heisenberg_fixes_isotropic_vector]

lemma one_parameter_element_base_vector (x x' : HPar k r') (c : ℂ) (g₁ : Mat k r') :
    oneStep k r' x c g₁ x' *ᵥ e0 k r' = mk3 k r' (c * hb k r' (-x.1) (-x.2)) (c • (-x.1)) c := by
  unfold oneStep
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, heisenberg_fixes_isotropic_vector, levi_fixes_isotropic_vector, long_weyl_element_base_vector, al_heis_inv, heisenberg_three_block]
  dsimp only
  rw [al_herm_zero_left]
  simp

lemma al_oneStep_mem (x x' : HPar k r') {c : ℂ} (hc : c ≠ 0) {g₁ : Mat k r'} (hg : g₁ ∈ GV k r') :
    oneStep k r' x c g₁ x' ∈ GV k (1 + r') := by
  unfold oneStep
  exact al_mul_mem (al_mul_mem (al_mul_mem (al_inv_mem (heis_mem x)) (cmHalfIntegralGenerator_mem_algebraicClosure c hc)) (lev_mem g₁ hg)) (heis_mem x')

theorem al_oneStepMem : OneStepMem := by
  unfold OneStepMem
  intro k r' x x' c hc g₁ hg
  exact ⟨al_oneStep_mem x x' hc hg, by rw [one_parameter_element_base_vector, al_cL_eq, three_block_last]⟩

lemma al_oneStep_inj {x x' z z' : HPar k r'} {c : ℂ} (hc : c ≠ 0) {g₁ h₁ : Mat k r'}
    (h : oneStep k r' x c g₁ x' = oneStep k r' z c h₁ z') : x = z ∧ g₁ = h₁ ∧ x' = z' := by
  have h0 := congrArg (fun A => A *ᵥ e0 k r') h
  simp only [one_parameter_element_base_vector] at h0
  obtain ⟨ha, hy, -⟩ := three_block_injective h0
  have hx1 : x.1 = z.1 := by
    have := smul_right_injective _ hc hy
    exact neg_injective this
  have hx2 : x.2 = z.2 := by
    have := congrArg Complex.im (mul_left_cancel₀ hc ha)
    rw [hb_im, hb_im] at this
    exact neg_injective this
  have hxz : x = z := Prod.ext hx1 hx2
  subst hxz
  have hA : IsUnit ((heis0 k r' x)⁻¹ * w0 k r' c).det := al_unit (al_mul_mem (al_inv_mem (heis_mem x)) (cmHalfIntegralGenerator_mem_algebraicClosure c hc))
  have h' : ιLev k 1 r' g₁ * heis0 k r' x' = ιLev k 1 r' h₁ * heis0 k r' z' := by
    unfold oneStep at h
    rw [Matrix.mul_assoc ((heis0 k r' x)⁻¹ * w0 k r' c), Matrix.mul_assoc ((heis0 k r' x)⁻¹ * w0 k r' c)] at h
    have := congrArg (fun B => ((heis0 k r' x)⁻¹ * w0 k r' c)⁻¹ * B) h
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hA] using this
  have hm : ∀ y, mk3 k r' (- herm (Hpk k r') y x'.1) (g₁ *ᵥ y) 0 = mk3 k r' (- herm (Hpk k r') y z'.1) (h₁ *ᵥ y) 0 := by
    intro y
    have := congrArg (fun A => A *ᵥ mk3 k r' 0 y 0) h'
    simp only [← Matrix.mulVec_mulVec, heisenberg_three_block, levi_three_block] at this
    simpa using this
  have hg : g₁ = h₁ := al_mat_ext fun y => (three_block_injective (hm y)).2.1
  have hy' : x'.1 = z'.1 := by
    have : x'.1 + -z'.1 = 0 := by
      apply herm_nondeg
      intro y
      rw [herm_add_right, al_herm_neg_right]
      have := (three_block_injective (hm y)).1
      linear_combination -this
    exact add_neg_eq_zero.1 this
  have hs' : x'.2 = z'.2 := by
    have := congrArg (fun A => A *ᵥ es0 k r') h'
    simp only [← Matrix.mulVec_mulVec, heisenberg_dual_base_vector, levi_three_block] at this
    have := congrArg Complex.im (three_block_injective this).1
    rwa [hb_im, hb_im] at this
  exact ⟨rfl, hg, Prod.ext hy' hs'⟩

lemma al_oneStep_exists {g : Mat k (1 + r')} (hg : g ∈ GV k (1 + r'))
    (hc : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') ≠ 0) :
    ∃ (x : HPar k r') (g₁ : Mat k r') (x' : HPar k r'), g₁ ∈ GV k r' ∧
      g = oneStep k r' x (herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r')) g₁ x' := by
  set c := herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') with hcdef
  have hcL : cL (g *ᵥ e0 k r') = c := by rw [hcdef, al_cL_eq]
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have hq : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (g *ᵥ e0 k r') = 0 := by
    rw [herm_UH _ hg, al_cL_eq, e0_eq, three_block_last]
  rw [← three_block_eta (g *ᵥ e0 k r'), hermitian_three_block, hcL] at hq
  set α := cF (g *ᵥ e0 k r') with hα
  set y' := mid (g *ᵥ e0 k r') with hy'
  have hbb : α / c = hb k r' (c⁻¹ • y') (α / c).im := by
    apply eq_hb
    rw [herm_smul_left, herm_smul_right, map_div₀, map_inv₀]
    field_simp
    linear_combination hq
  set x₁ : HPar k r' := (c⁻¹ • y', (α / c).im) with hx₁
  have hn := heis_mem x₁
  have hw := cmHalfIntegralGenerator_mem_algebraicClosure (k := k) (r' := r') c hc
  have hu : heis0 k r' x₁ *ᵥ mk3 k r' 0 0 c = g *ᵥ e0 k r' := by
    rw [heisenberg_three_block, ← three_block_eta (g *ᵥ e0 k r'), hcL, ← hα, ← hy']
    have e1 : (0 : ℂ) - herm (Hpk k r') 0 x₁.1 + c * hb k r' x₁.1 x₁.2 = α := by
      rw [al_herm_zero_left, ← hbb]; field_simp; ring
    have e2 : (0 : Fin (2 * r' + k + 1) → ℂ) + c • x₁.1 = y' := by
      rw [zero_add, hx₁, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [e1, e2]
  set p := (w0 k r' c)⁻¹ * ((heis0 k r' x₁)⁻¹ * g) with hp
  have hpm : p ∈ GV k (1 + r') := al_mul_mem (al_inv_mem hw) (al_mul_mem (al_inv_mem hn) hg)
  have hpe : p *ᵥ e0 k r' = e0 k r' := by
    rw [hp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, al_inv_mulVec (al_unit hn) hu]
    exact al_inv_mulVec (al_unit hw) (long_weyl_element_base_vector c)
  have hpi : p⁻¹ ∈ P1set k r' := ⟨al_inv_mem hpm, al_inv_mulVec (al_unit hpm) hpe⟩
  rw [al_stabDecomp k r'] at hpi
  obtain ⟨n, ⟨x'', rfl⟩, l, ⟨g₁, hg₁, rfl⟩, hpp⟩ := hpi
  have hp2 : p = ιLev k 1 r' g₁⁻¹ * heis0 k r' (-x''.1, -x''.2) := by
    rw [← Matrix.nonsing_inv_nonsing_inv p (al_unit hpm), hpp, Matrix.mul_inv_rev, al_heis_inv, al_lev_inv (al_unit hg₁)]
  refine ⟨(-x₁.1, -x₁.2), g₁⁻¹, (-x''.1, -x''.2), al_inv_mem hg₁, ?_⟩
  unfold oneStep
  rw [al_heis_inv]
  simp only [neg_neg, Prod.mk.eta]
  rw [Matrix.mul_assoc (heis0 k r' x₁ * w0 k r' c), ← hp2, hp, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ (al_unit hw), Matrix.mul_nonsing_inv_cancel_left _ _ (al_unit hn)]

theorem al_oneStepCoord : OneStepCoord := by
  intro k r' g hg hc
  obtain ⟨x, g₁, x', hg₁, he⟩ := al_oneStep_exists hg hc
  refine ⟨(x, g₁, x'), ⟨hg₁, he⟩, ?_⟩
  rintro ⟨z, h₁, z'⟩ ⟨-, hz⟩
  simp only at hz
  obtain ⟨e1, e2, e3⟩ := al_oneStep_inj hc (hz.symm.trans he)
  rw [e1, e2, e3]

lemma al_phi (g : Mat k (1 + r')) (w : Fin (2 * (1 + r') + k + 1) → ℂ) (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' a y b) w =
      a * herm (Hpk k (1 + r')) (g *ᵥ e0 k r') w + herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' 0 y 0) w +
        b * herm (Hpk k (1 + r')) (g *ᵥ es0 k r') w := by
  rw [three_block_split a b y]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, herm_add_left, herm_smul_left]

theorem gen_induction (P : Mat k (1 + r') → Prop) (hmul : ∀ a b, P a → P b → P (a * b))
    (hcancel : ∀ a b, P (a * b) → P b → P a)
    (hH : ∀ x, P (heis0 k r' x)) (hw : ∀ c, c ≠ 0 → P (w0 k r' c)) (hl : ∀ g₁ ∈ GV k r', P (ιLev k 1 r' g₁)) :
    ∀ g ∈ GV k (1 + r'), P g := by
  have big : ∀ g ∈ GV k (1 + r'), herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') ≠ 0 → P g := by
    intro g hg hc
    obtain ⟨x, g₁, x', hg₁, he⟩ := al_oneStep_exists hg hc
    rw [he]
    unfold oneStep
    rw [al_heis_inv]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hH _) (hw _ hc)) (hl _ hg₁)) (hH _)
  intro g hg
  by_cases hc : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') = 0
  · have hex : ∃ x : HPar k r', herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' (hb k r' x.1 x.2) x.1 1) (e0 k r') ≠ 0 := by
      by_contra hno
      push Not at hno
      have h1 : ∀ y, herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' 0 y 0) (e0 k r') +
          herm (Hpk k (1 + r')) (g *ᵥ es0 k r') (e0 k r') = 0 := by
        intro y
        have := hno (y, 0)
        rw [al_phi, hc] at this
        simpa using this
      have h2 : herm (Hpk k (1 + r')) (g *ᵥ es0 k r') (e0 k r') = 0 := by
        have := h1 0
        have hz : mk3 k r' 0 0 0 = 0 := by rw [← lift_eq]; ext i; simp [liftVec]
        rw [hz, Matrix.mulVec_zero, al_herm_zero_left, zero_add] at this
        exact this
      have h3 : ∀ u, herm (Hpk k (1 + r')) (g *ᵥ u) (e0 k r') = 0 := by
        intro u
        rw [← three_block_eta u, al_phi, hc, h2]
        have := h1 (mid u)
        rw [h2, add_zero] at this
        rw [this]; simp
      have h4 := h3 (g⁻¹ *ᵥ es0 k r')
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (al_unit hg), Matrix.one_mulVec, al_cL_eq, dual_base_vector_eq_single, three_block_last] at h4
      exact one_ne_zero h4
    obtain ⟨x, hx⟩ := hex
    have hPh : P (heis0 k r' x * w0 k r' 1) := hmul _ _ (hH x) (hw 1 one_ne_zero)
    apply hcancel g (heis0 k r' x * w0 k r' 1) _ hPh
    apply big _ (al_mul_mem hg (al_mul_mem (heis_mem x) (cmHalfIntegralGenerator_mem_algebraicClosure 1 one_ne_zero)))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, long_weyl_element_base_vector, ← dual_base_vector_eq_single, heisenberg_dual_base_vector]
    exact hx
  · exact big g hg hc

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P

theorem stabilizer_one_parameter_mem : Formalism.FourierDecayAlt.B2.OneStepMem := Formalism.FourierDecayAlt.P.B2x8.al_oneStepMem
theorem rank_one_coordinates_formula : Formalism.FourierDecayAlt.B2.OneStepCoord := Formalism.FourierDecayAlt.P.B2x8.al_oneStepCoord
theorem stabilizer_factorization : Formalism.FourierDecayAlt.B2.StabDecomp := Formalism.FourierDecayAlt.P.B2x8.al_stabDecomp

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

lemma cf_hb_neg (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : hb k r' y (-s) = conj (hb k r' y s) := by
  apply Complex.ext
  · rw [Complex.conj_re, hb_re, hb_re]
  · rw [Complex.conj_im, hb_im, hb_im]

lemma cf_hb_ne (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) (hs : s ≠ 0) : hb k r' y s ≠ 0 := by
  intro h
  apply hs
  have := hb_im y s
  rw [h] at this
  simpa using this.symm

lemma long_weyl_parametrisation_twist (c₀ : ℂ) (hc : c₀ ≠ 0) (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) (h2 : p.2.2 ≠ 0) :
    w0 k r' c₀ *ᵥ Ψt k r' p = Ψt k r' (Tw k r' c₀ p) := by
  simp only [Ψt, Tw, long_weyl_three_block]
  have hh : hb k r' p.2.1 p.2.2 ≠ 0 := cf_hb_ne p.2.1 p.2.2 h2
  have hh' : (starRingEnd ℂ) (hb k r' p.2.1 p.2.2) ≠ 0 := by simpa using hh
  have hc' : (starRingEnd ℂ) c₀ ≠ 0 := by simpa using hc
  rw [cf_hb_neg]
  congr 1
  · simp only [map_div₀, map_mul, Complex.conj_conj]
    field_simp
  · ring

lemma cf_lev_Ψt (g₁ : Mat k r') (hg : g₁ ∈ GV k r') (p : ℂ × HPar k r') :
    ιLev k 1 r' g₁ *ᵥ Ψt k r' p = Ψt k r' (Tl k r' g₁ p) := by
  simp only [Ψt, Tl, levi_three_block]
  rw [show hb k r' (g₁ *ᵥ p.2.1) p.2.2 = hb k r' p.2.1 p.2.2 by simp only [hb, herm_UH _ hg]]

lemma cf_heis_Ψt (x₀ : HPar k r') (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) :
    heis0 k r' x₀ *ᵥ Ψt k r' p = Ψt k r' (Tn k r' x₀ p) := by
  obtain ⟨c, y, s⟩ := p
  obtain ⟨y₀, s₀⟩ := x₀
  have hp1 : conj c ≠ 0 := (map_ne_zero _).2 h1
  unfold Ψt Tn
  rw [heisenberg_three_block]
  dsimp only at h1 ⊢
  set B : ℂ := hb k r' y s - conj c * herm (Hpk k r') y y₀ + (‖c‖ ^ 2 : ℝ) * hb k r' y₀ s₀ with hB
  have hnorm : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsum : B + conj B = - herm (Hpk k r') (y + c • y₀) (y + c • y₀) := by
    have e1 := hb_add_conj (k := k) (r' := r') y s
    have e2 := hb_add_conj (k := k) (r' := r') y₀ s₀
    have e3 : conj (herm (Hpk k r') y y₀) = herm (Hpk k r') y₀ y := herm_conj _ (Hpk_herm k r') _ _
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
    rw [hB]
    simp only [map_add, map_sub, map_mul, Complex.conj_conj, Complex.conj_ofReal, e3]
    rw [hnorm]
    linear_combination e1 + c * conj c * e2
  have him : B.im = s - (conj c * herm (Hpk k r') y y₀).im + ‖c‖ ^ 2 * s₀ := by
    rw [hB]
    simp only [Complex.add_im, Complex.sub_im, hb_im, Complex.im_ofReal_mul]
  have hBB := eq_hb hsum
  rw [him] at hBB
  rw [← hBB]
  congr 1
  rw [hB, hnorm]
  field_simp

lemma ae_first_coordinate_ne_zero : ∀ᵐ p : ℂ × HPar k r' ∂(μx.prod (volume : Measure (HPar k r'))), p.1 ≠ 0 := by
  rw [ae_iff]
  have h0 : μx {(0 : ℂ)} = 0 := (withDensity_absolutelyContinuous _ _) (measure_singleton 0)
  have : {p : ℂ × HPar k r' | ¬ p.1 ≠ 0} = {(0 : ℂ)} ×ˢ Set.univ := by ext p; simp
  rw [this, Measure.prod_prod, h0, zero_mul]

lemma ae_heisenberg_parameter_ne_zero : ∀ᵐ p : ℂ × HPar k r' ∂(μx.prod (volume : Measure (HPar k r'))), p.2.2 ≠ 0 := by
  rw [ae_iff]
  have h0 := ae_second_coordinate_ne_zero (k := k) (r' := r')
  rw [ae_iff] at h0
  have : {p : ℂ × HPar k r' | ¬ p.2.2 ≠ 0} = Set.univ ×ˢ {q : HPar k r' | ¬ q.2 ≠ 0} := by ext p; simp
  rw [this, Measure.prod_prod, h0, mul_zero]

lemma cf_mulVec_meas (g : Mat k (1 + r')) : Measurable fun x : Fin (2 * (1 + r') + k + 1) → ℂ => g *ᵥ x := (continuous_const.matrix_mulVec continuous_id).measurable

lemma cf_inv_of (g : Mat k (1 + r')) (T : ℂ × HPar k r' → ℂ × HPar k r')
    (hT : MeasurePreserving T (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))))
    (h : ∀ᵐ p ∂(μx.prod (volume : Measure (HPar k r'))), g *ᵥ Ψt k r' p = Ψt k r' (T p)) :
    (coneMeas k r').map (fun x => g *ᵥ x) = coneMeas k r' := by
  rw [cone_eq, Measure.map_map (cf_mulVec_meas g) Ψt_meas]
  rw [Measure.map_congr (show (fun x => g *ᵥ x) ∘ Ψt k r' =ᵐ[μx.prod (volume : Measure (HPar k r'))] Ψt k r' ∘ T from h)]
  rw [← Measure.map_map Ψt_meas hT.measurable, hT.map_eq]

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8

theorem isotropic_cone_invariance : Formalism.FourierDecayAlt.B2.ConeInv := by
  unfold Formalism.FourierDecayAlt.B2.ConeInv
  intro k r' g hg
  have e : ∀ a b : Mat k (1 + r'), (fun x => (a * b) *ᵥ x) = (fun x => a *ᵥ x) ∘ (fun x => b *ᵥ x) := by
    intro a b; funext x; simp [Matrix.mulVec_mulVec]
  refine B2x8.gen_induction (fun g => (coneMeas k r').map (fun x => g *ᵥ x) = coneMeas k r') ?_ ?_ ?_ ?_ ?_ g hg
  · intro a b ha hb'
    try dsimp only at ha hb' ⊢
    rw [e, ← Measure.map_map (B2x8.cf_mulVec_meas a) (B2x8.cf_mulVec_meas b), hb', ha]
  · intro a b hab hb'
    try dsimp only at hab hb' ⊢
    rw [e, ← Measure.map_map (B2x8.cf_mulVec_meas a) (B2x8.cf_mulVec_meas b), hb'] at hab
    exact hab
  · intro x
    exact B2x8.cf_inv_of _ _ (B2x8.Tn_mp x) (B2x8.ae_first_coordinate_ne_zero.mono fun p hp => B2x8.cf_heis_Ψt x p hp)
  · intro c hc
    exact B2x8.cf_inv_of _ _ (B2x8.Tw_mp c hc)
      ((B2x8.ae_first_coordinate_ne_zero.and B2x8.ae_heisenberg_parameter_ne_zero).mono fun p hp => B2x8.long_weyl_parametrisation_twist c hc p hp.1 hp.2)
  · intro g₁ hg₁
    exact B2x8.cf_inv_of _ _ (B2x8.Tl_mp g₁ hg₁) (Filter.Eventually.of_forall fun p => B2x8.cf_lev_Ψt g₁ hg₁ p)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

def cgS (k r' : ℕ) (R : ℝ) : Set (ℂ × HPar k r') := {p | ‖p.1‖ ≤ R ∧ ‖p.2.1‖ ≤ R ∧ |p.2.2| ≤ R * ‖p.1‖}

lemma cg_closed (R : ℝ) : IsClosed (cgS k r' R) := by
  show IsClosed ({p : ℂ × HPar k r' | ‖p.1‖ ≤ R} ∩ ({p | ‖p.2.1‖ ≤ R} ∩ {p | |p.2.2| ≤ R * ‖p.1‖}))
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;> exact isClosed_le (by fun_prop) (by fun_prop)

lemma cg_mem (R : ℝ) (hR : 0 ≤ R) (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) (h : ‖Ψt k r' p‖ ≤ R) : p ∈ cgS k r' R := by
  have hall : ∀ i, ‖Ψt k r' p i‖ ≤ R := fun i => (norm_le_pi_norm _ i).trans h
  have hL : cL (Ψt k r' p) = p.1 := by unfold Ψt; rw [three_block_last]
  have hM : mid (Ψt k r' p) = p.2.1 := by unfold Ψt; rw [three_block_middle]
  have hF : cF (Ψt k r' p) = hb k r' p.2.1 p.2.2 / conj p.1 := by unfold Ψt; rw [three_block_first]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hL]; exact hall _
  · rw [← hM, pi_norm_le_iff_of_nonneg hR]; intro j; exact hall _
  · have h3 : ‖hb k r' p.2.1 p.2.2 / conj p.1‖ ≤ R := by rw [← hF]; exact hall _
    rw [norm_div, RCLike.norm_conj, div_le_iff₀ (norm_pos_iff.2 h1)] at h3
    refine le_trans ?_ h3
    have := Complex.abs_im_le_norm (hb k r' p.2.1 p.2.2)
    rwa [hb_im] at this

lemma cg_finite (R : ℝ) (hR : 0 ≤ R) : (μx.prod (volume : Measure (HPar k r'))) (cgS k r' R) < ∞ := by
  rw [Measure.prod_apply (cg_closed R).measurableSet]
  set V : ℝ≥0∞ := volume (Metric.closedBall (0 : Fin (2 * r' + k + 1) → ℂ) R) with hV
  have hVfin : V < ∞ := measure_closedBall_lt_top
  have hslice : ∀ c : ℂ, (volume : Measure (HPar k r')) (Prod.mk c ⁻¹' cgS k r' R) ≤
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => V * ENNReal.ofReal (2 * R * ‖c‖)) c := by
    intro c
    by_cases hc : ‖c‖ ≤ R
    · rw [Set.indicator_of_mem (by simpa using hc)]
      have : Prod.mk c ⁻¹' cgS k r' R ⊆
          Metric.closedBall (0 : Fin (2 * r' + k + 1) → ℂ) R ×ˢ Set.Icc (-(R * ‖c‖)) (R * ‖c‖) := by
        rintro q ⟨_, h2, h3⟩
        exact ⟨by simpa using h2, abs_le.1 h3⟩
      refine (measure_mono this).trans ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
      apply le_of_eq; congr 2; ring
    · have : Prod.mk c ⁻¹' cgS k r' R = ∅ := by
        ext q; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, _⟩; exact hc h1
      rw [this]; simp
  refine (lintegral_mono hslice).trans_lt ?_
  have hmeas : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (fun c => V * ENNReal.ofReal (2 * R * ‖c‖))) := by
    refine Measurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
    fun_prop
  unfold μx
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hmeas]
  have hpt : ∀ c : ℂ, ((fun c : ℂ => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹)) *
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => V * ENNReal.ofReal (2 * R * ‖c‖))) c =
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => (V * ENNReal.ofReal (2 * R)) * ENNReal.ofReal (‖c‖⁻¹)) c := by
    intro c
    rw [Pi.mul_apply]
    by_cases hc : c ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc]
      have e : (‖c‖ ^ 2)⁻¹ * (2 * R * ‖c‖) = 2 * R * ‖c‖⁻¹ := by
        by_cases h0 : ‖c‖ = 0
        · simp [h0]
        · field_simp
      have a : ENNReal.ofReal ((‖c‖ ^ 2)⁻¹) * ENNReal.ofReal (2 * R * ‖c‖) =
          ENNReal.ofReal (2 * R) * ENNReal.ofReal (‖c‖⁻¹) := by
        rw [← ENNReal.ofReal_mul (by positivity), e, ENNReal.ofReal_mul (by positivity)]
      rw [mul_left_comm, a, mul_assoc]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, mul_zero]
  rw [lintegral_congr hpt, lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    lintegral_const_mul' _ _ (ENNReal.mul_lt_top hVfin ENNReal.ofReal_lt_top).ne]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hVfin ENNReal.ofReal_lt_top) (lintegral_inv_norm_lt_top R)

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8

theorem isotropic_cone_finite_measure : Formalism.FourierDecayAlt.B2.ConeFinite := by
  unfold Formalism.FourierDecayAlt.B2.ConeFinite
  intro k r' K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [B2x8.cone_eq]
  refine lt_of_le_of_lt ?_ (B2x8.cg_finite (k := k) (r' := r') (max R 0) (le_max_right _ _))
  refine le_trans (measure_mono (hR.trans (Metric.closedBall_subset_closedBall (le_max_left R 0)))) ?_
  rw [Measure.map_apply B2x8.Ψt_meas measurableSet_closedBall]
  have hnull : (B2x8.μx.prod (volume : Measure (HPar k r'))) {p | ¬ p.1 ≠ 0} = 0 := ae_iff.mp B2x8.ae_first_coordinate_ne_zero
  have hsub : B2x8.Ψt k r' ⁻¹' Metric.closedBall 0 (max R 0) ⊆ B2x8.cgS k r' (max R 0) ∪ {p | ¬ p.1 ≠ 0} := by
    intro p hpK
    by_cases hp : p.1 ≠ 0
    · exact Or.inl (B2x8.cg_mem (max R 0) (le_max_right _ _) p hp (by simpa using hpK))
    · exact Or.inr hp
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  rw [hnull, add_zero]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.B2x8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section dj
variable {k r : ℕ}

lemma dj_conjM_cont (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact ((continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

lemma dj_mulM_cont : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  exact Continuous.matrix_mul (A := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r))
    (B := fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) continuous_fst continuous_snd

lemma dj_levM_cont (k r' : ℕ) : Continuous (levM k r') := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  unfold levM ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [hp, hq, dif_pos, and_self]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [hp, hq, dif_pos, dif_neg, and_self, not_false_eq_true]
      exact continuous_const
  · simp only [hp, dif_neg, not_false_eq_true]
    exact continuous_const

lemma dj_aDil_unit (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : IsUnit (aDil k r t).det := by
  unfold aDil
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact_mod_cast pow_ne_zero _ ht
  · exact one_ne_zero
  · exact_mod_cast inv_ne_zero (pow_ne_zero _ ht)

lemma dj_conj_mul (a : Mat k r) (ha : IsUnit a.det) (p : Mt k r × Mt k r) :
    conjM a (mulM p) = mulM (conjM a p.1, conjM a p.2) := by
  unfold conjM mulM
  show a * (Matrix.of p.1 * Matrix.of p.2) * a⁻¹ = (a * Matrix.of p.1 * a⁻¹) * (a * Matrix.of p.2 * a⁻¹)
  have h : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  calc a * (Matrix.of p.1 * Matrix.of p.2) * a⁻¹ = a * Matrix.of p.1 * 1 * Matrix.of p.2 * a⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = (a * Matrix.of p.1 * a⁻¹) * (a * Matrix.of p.2 * a⁻¹) := by
        rw [← h]; simp only [Matrix.mul_assoc]

lemma dj_sigmaFinite {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

lemma dj_step (hU : HaarUnique) (hN : ClosedN) (hRec : NRecHaar) (hLev : DilLev) (hH : DilHeisMeas) (hK : KapRec)
    (k r' : ℕ) (μ' : Measure (Mt k r')) (hμ' : IsHaarOn (Nset k r') μ')
    (ih : ∀ t : ℝ, 0 < t → μ'.map (conjM (aDil k r' t)) = ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ')
    (μN : Measure (Mt k (1 + r'))) (hμN : IsHaarOn (Nset k (1 + r')) μN) (t : ℝ) (ht : 0 < t) :
    μN.map (conjM (aDil k (1 + r') t)) = ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • μN := by
  have := dj_sigmaFinite hμ'
  have hvol : SFinite (volume : Measure (HPar k r')) := by rw [Measure.volume_eq_prod]; infer_instance
  have : SFinite (μHeis k r') := by
    unfold μHeis
    exact @MeasureTheory.Measure.instSFiniteMap _ _ _ _ _ _ hvol
  have hν := hRec k r' μ' hμ'
  obtain ⟨c, hc⟩ := hU k (1 + r') (Nset k (1 + r')) _ μN (hN _ _) hν hμN.conc hμN.left hμN.finite_compact
  have hca := (dj_conjM_cont (aDil k (1 + r') t)).measurable
  have hca' := (dj_conjM_cont (aDil k r' t)).measurable
  have hlev := (dj_levM_cont k r').measurable
  have hmul := (dj_mulM_cont (k := k) (r := 1 + r')).measurable
  have key : (((μHeis k r').prod (μ'.map (levM k r'))).map mulM).map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • ((μHeis k r').prod (μ'.map (levM k r'))).map mulM := by
    have h1 : (conjM (aDil k (1 + r') t) ∘ mulM : Mt k (1 + r') × Mt k (1 + r') → Mt k (1 + r')) =
        mulM ∘ Prod.map (conjM (aDil k (1 + r') t)) (conjM (aDil k (1 + r') t)) := by
      funext p
      exact dj_conj_mul _ (dj_aDil_unit _ _ _ ht.ne') p
    have h2 : (μ'.map (levM k r')).map (conjM (aDil k (1 + r') t)) =
        ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ'.map (levM k r') := by
      rw [Measure.map_map hca hlev]
      have : (conjM (aDil k (1 + r') t) ∘ levM k r') = levM k r' ∘ conjM (aDil k r' t) := by
        funext x
        exact hLev k r' t ht.ne' (Matrix.of x)
      rw [this, ← Measure.map_map hlev hca', ih t ht, Measure.map_smul]
    rw [Measure.map_map hca hmul, h1, ← Measure.map_map hmul (hca.prodMap hca), ← Measure.map_prod_map _ _ hca hca,
      h2, hH k r' t ht, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul,
      hK k r', pow_add, mul_inv, ENNReal.ofReal_mul (by positivity)]
  rw [hc, Measure.map_smul, key, smul_comm]

end dj

end Formalism.FourierDecayAlt.P.B2x8

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x8

theorem dilation_jacobian_of_parts : Formalism.FourierDecayAlt.B2.AssembleDilJac := by
  intro hU hN hRec _ hEx hLev hH hK
  have raw : DilJacRaw := by
    intro k r
    induction r with
    | zero =>
      intro μN _ t _
      have h1 : aDil k 0 t = 1 := by
        unfold aDil
        rw [← Matrix.diagonal_one]
        congr 1
        funext i
        have := i.isLt
        rw [if_neg (by omega), if_pos (by omega)]
      have h2 : (conjM (1 : Mat k 0) : Mt k 0 → Mt k 0) = id := by
        funext x
        simp [conjM]
        rfl
      have h3 : kap k 0 = 0 := by simp [kap]
      rw [h1, h2, h3]
      simp
    | succ r' ih =>
      rw [Nat.add_comm r' 1]
      intro μN hμN t ht
      obtain ⟨μ', hμ'⟩ := hEx k r'
      exact dj_step hU hN hRec hLev hH hK k r' μ' hμ' (ih μ' hμ') μN hμN t ht
  exact ⟨raw, fun k r Wp Wq _ _ _ _ D t ht => raw k r D.μN D.haarN t ht⟩

end Formalism.FourierDecayAlt.P
