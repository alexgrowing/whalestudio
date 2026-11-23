import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLeOfNonarch
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCmp

variable {K : Type} [Field K] (w : AbsoluteValue K ℝ)

theorem sum_le (hw : IsNonarchimedean w) {ι : Type} (s : Finset ι) (f : ι → K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∈ s, w (f i) ≤ c) : w (∑ i ∈ s, f i) ≤ c := by
  first
  | exact @_root_.GlobalTheory.NonarchimedeanSumBound.main
  | exact _root_.GlobalTheory.NonarchimedeanSumBound.main
  | (apply _root_.GlobalTheory.NonarchimedeanSumBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonarchimedeanSumBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonarchimedeanSumBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonarchimedeanSumBound.main ..)

theorem sub_le (hw : IsNonarchimedean w) (x y : K) {c : ℝ} (hx : w x ≤ c) (hy : w y ≤ c) : w (x - y) ≤ c := by
  rw [sub_eq_add_neg]
  exact (hw _ _).trans (max_le hx (by rw [w.map_neg]; exact hy))

theorem mul_le (hw : IsNonarchimedean w) {m n o : Type} [Fintype n] (A : Matrix m n K) (B : Matrix n o K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : ∀ i j, w (A i j) ≤ a) (hB : ∀ i j, w (B i j) ≤ b) (i : m) (k : o) :
    w ((A * B) i k) ≤ a * b := by
  rw [Matrix.mul_apply]
  exact sum_le w hw _ _ (mul_nonneg ha hb) fun j _ => by
    rw [map_mul]; exact mul_le_mul (hA i j) (hB j k) (w.nonneg _) ha

theorem det_le (hw : IsNonarchimedean w) {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K)
    (hA : ∀ i j, w (A i j) ≤ 1) : w A.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine sum_le w hw _ _ zero_le_one fun σ _ => ?_
  have hp : w (∏ i, A (σ i) i) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one (fun i _ => w.nonneg _) fun i _ => hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, w.map_neg]

theorem inv_le (hw : IsNonarchimedean w) {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K)
    (hA : ∀ i j, w (A i j) ≤ 1) (hd : w A.det = 1) (i j : n) : w (A⁻¹ i j) ≤ 1 := by
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, map_mul, map_inv₀, hd, inv_one,
    one_mul, Matrix.adjugate_apply]
  refine det_le w hw _ fun k l => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs <;> simp
  · exact hA k l

theorem scale {n : ℕ} (x : Fin n → K) {r : ℝ} (hr : 1 ≤ r) (hx : ∀ j, w (x j) ≤ r) :
    ∃ c : K, c ≠ 0 ∧ w c ≤ r ∧ ∀ j, w (c⁻¹ * x j) ≤ 1 := by
  by_cases h : ∀ j, w (x j) ≤ 1
  · exact ⟨1, one_ne_zero, by simpa using hr, fun j => by simpa using h j⟩
  push_neg at h
  obtain ⟨j0, hj0⟩ := h
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => w (x j)) ⟨j0, Finset.mem_univ _⟩
  have hk1 : 1 < w (x k) := hj0.trans_le (hk j0 (Finset.mem_univ _))
  have hk0 : x k ≠ 0 := fun e => by rw [e, map_zero] at hk1; linarith
  refine ⟨x k, hk0, hx k, fun j => ?_⟩
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ (w.pos hk0), mul_one]
  exact hk j (Finset.mem_univ _)

theorem iso_scale {g n : ℕ} (H : Matrix (Fin n) (Fin g) K) (J : Matrix (Fin n) (Fin n) K) {ε r : ℝ} (hr : 1 ≤ r)
    (hε : 0 ≤ ε)
    (hiso : ∀ u u' : Fin g → K, supN w (H.mulVec u) ≤ 1 → supN w (H.mulVec u') ≤ 1 →
      w (dotProduct (H.mulVec u) (J.mulVec (H.mulVec u'))) ≤ ε)
    (u u' : Fin g → K) (hu : ∀ j, w (H.mulVec u j) ≤ r) (hu' : ∀ j, w (H.mulVec u' j) ≤ r) :
    w (dotProduct (H.mulVec u) (J.mulVec (H.mulVec u'))) ≤ r * r * ε := by
  obtain ⟨c, hc0, hcr, hc⟩ := scale w _ hr hu
  obtain ⟨c', hc0', hcr', hc'⟩ := scale w _ hr hu'
  have h1 := hiso (c⁻¹ • u) (c'⁻¹ • u')
    (supN_le w zero_le_one fun j => by rw [Matrix.mulVec_smul]; exact hc j)
    (supN_le w zero_le_one fun j => by rw [Matrix.mulVec_smul]; exact hc' j)
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, map_mul, map_mul, map_inv₀, map_inv₀] at h1
  have hc1 := w.pos hc0
  have hc2 := w.pos hc0'
  have e : w (dotProduct (H.mulVec u) (J.mulVec (H.mulVec u'))) ≤ w c * w c' * ε := by
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc1.le hc2.le)
    calc _ = w c * w c' * ((w c)⁻¹ * ((w c')⁻¹ * w (dotProduct (H.mulVec u) (J.mulVec (H.mulVec u'))))) := by
          field_simp
      _ ≤ _ := this
  exact e.trans (mul_le_mul_of_nonneg_right (mul_le_mul hcr hcr' hc2.le (by linarith)) hε)

theorem agree_scale {g n : ℕ} (H H' : Matrix (Fin n) (Fin g) K) {ε r : ℝ} (hr : 1 ≤ r)
    (hag : ∀ u : Fin g → K, supN w (H.mulVec u) ≤ 1 → supN w (H'.mulVec u - H.mulVec u) ≤ ε)
    (u : Fin g → K) (hu : ∀ j, w (H.mulVec u j) ≤ r) (j : Fin n) :
    w (H'.mulVec u j - H.mulVec u j) ≤ r * ε := by
  obtain ⟨c, hc0, hcr, hc⟩ := scale w _ hr hu
  have h1 := (le_supN w _ j).trans
    (hag (c⁻¹ • u) (supN_le w zero_le_one fun j => by rw [Matrix.mulVec_smul]; exact hc j))
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, ← mul_sub, map_mul, map_inv₀, inv_mul_le_iff₀ (w.pos hc0)] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right hcr ((w.nonneg _).trans ((le_supN w _ j).trans
    (hag (c⁻¹ • u) (supN_le w zero_le_one fun j => by rw [Matrix.mulVec_smul]; exact hc j)))))

theorem tri_mul_diag {g : ℕ} (A C : Matrix (Fin g) (Fin g) K) (hA : A.BlockTriangular id)
    (hC : C.BlockTriangular id) (l : Fin g) : (A * C) l l = A l l * C l l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · intro m _ hm
    rcases lt_or_gt_of_ne hm with h | h
    · rw [hA h, zero_mul]
    · rw [hC h, mul_zero]
  · simp

theorem bilin_apply {m n o : Type} [Fintype m] (A : Matrix m n K) (J : Matrix m m K) (B : Matrix m o K) (a : n) (b : o) :
    (A.transpose * J * B) a b = dotProduct (fun i => A i a) (J.mulVec fun i => B i b) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frame_change_tri : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ {g : ℕ}
    (Ub U' Ha Hb : Matrix (Fin (g + g)) (Fin g) K) (Lb L' : Matrix (Fin g) (Fin (g + g)) K)
    (J Ji Ji' P Q : Matrix (Fin (g + g)) (Fin (g + g)) K) (Bb B' : Matrix (Fin g) (Fin g) K) (η ε : ℝ),
    0 < η → η ≤ 1 → 0 ≤ ε → P * Q = 1 → J * Ji = 1 → Q.transpose * J * Q * Ji' = 1 → Lb * Ub = 1 → L' * U' = 1 →
    Bb.BlockTriangular id → B'.BlockTriangular id → (∀ i, Bb i i ≠ 0) → (∀ i, B' i i ≠ 0) →
    Ub = Hb * Bb → U' = P * Ha * B' → (∀ i j, w (J i j) ≤ 1) → (∀ i j, w (P i j) ≤ η⁻¹ ∧ w (Q i j) ≤ η⁻¹) →
    (∀ i j, w (compl Ub Lb Ji i j) ≤ 1) → (∀ i j, w (compl U' L' Ji' i j) ≤ 1) → w (compl U' L' Ji').det = 1 →
    (∀ u u' : Fin g → K, supN w (Ha.mulVec u) ≤ 1 → supN w (Ha.mulVec u') ≤ 1 →
      w (dotProduct (Ha.mulVec u) (J.mulVec (Ha.mulVec u'))) ≤ ε) →
    (∀ u : Fin g → K, supN w (Ha.mulVec u) ≤ 1 → supN w (Hb.mulVec u - Ha.mulVec u) ≤ ε) →
    (∀ u : Fin g → K, supN w (Hb.mulVec u) ≤ 1 → supN w (Ha.mulVec u - Hb.mulVec u) ≤ ε) →
    ∀ i : Fin (g + g), (∀ j, j < i → w (((compl U' L' Ji')⁻¹ * P * compl Ub Lb Ji) i j) ≤ ε / η ^ 3) ∧
      w (((compl U' L' Ji')⁻¹ * P * compl Ub Lb Ji) i i -
        Fin.addCases (motive := fun _ => K) (fun l => Bb l l / B' l l) (fun l => B' l.rev l.rev / Bb l.rev l.rev) i) ≤
        ε / η ^ 3 := by
  intro K _ w hw g Ub U' Ha Hb Lb L' J Ji Ji' P Q Bb B' η ε hη hη1 hε hPQ hJ hJ' hLU hLU' hBb hB' hBb0 hB'0 hUb hU'
    hJle hPQle hM hM' hdet hiso hag1 hag2
  set M := compl Ub Lb Ji with hMd
  set M' := compl U' L' Ji' with hM'd
  set X := M'⁻¹ * P * M with hXd
  let S : Matrix (Fin (g + g)) (Fin g) K := Matrix.of fun k l => if k = Fin.castAdd g l then 1 else 0
  let T : Matrix (Fin (g + g)) (Fin g) K := Matrix.of fun k l => if k = Fin.natAdd g l then 1 else 0
  let Rv : Matrix (Fin g) (Fin g) K := Matrix.of fun a b => if a = b.rev then 1 else 0
  have hcn : ∀ a b : Fin g, Fin.castAdd g a ≠ Fin.natAdd g b := fun a b h => by
    have := congrArg Fin.val h; simp at this; omega
  have hnc : ∀ a b : Fin g, Fin.natAdd g a ≠ Fin.castAdd g b := fun a b h => hcn b a h.symm
  have hAS : ∀ {o : Type} (A : Matrix o (Fin (g + g)) K) i l, (A * S) i l = A i (Fin.castAdd g l) := by
    intro o A i l; simp [S, Matrix.mul_apply]
  have hAT : ∀ {o : Type} (A : Matrix o (Fin (g + g)) K) i l, (A * T) i l = A i (Fin.natAdd g l) := by
    intro o A i l; simp [T, Matrix.mul_apply]
  have hSA : ∀ {o : Type} (A : Matrix (Fin (g + g)) o K) l k, (S.transpose * A) l k = A (Fin.castAdd g l) k := by
    intro o A l k; simp [S, Matrix.mul_apply]
  have hTA : ∀ {o : Type} (A : Matrix (Fin (g + g)) o K) l k, (T.transpose * A) l k = A (Fin.natAdd g l) k := by
    intro o A l k; simp [T, Matrix.mul_apply]
  have hMS : M * S = Ub := by ext i l; rw [hAS]; simp [M, ConstLat.compl]
  have hM'S : M' * S = U' := by ext i l; rw [hAS]; simp [M', ConstLat.compl]
  have hRvr : ∀ {o : Type} (A : Matrix o (Fin g) K) i l, (A * Rv) i l = A i l.rev := by
    intro o A i l
    rw [Matrix.mul_apply, Finset.sum_eq_single l.rev]
    · simp [Rv]
    · intro b _ hb; simp [Rv, hb]
    · simp
  have hRvl : ∀ {o : Type} (A : Matrix (Fin g) o K) l k, (Rv * A) l k = A l.rev k := by
    intro o A l k
    rw [Matrix.mul_apply, Finset.sum_eq_single l.rev]
    · simp [Rv]
    · intro b _ hb
      have : l ≠ b.rev := fun h => hb (by rw [h, Fin.rev_rev])
      simp [Rv, this]
    · simp
  have hSc : ∀ {o : Type} (A : Matrix o (Fin g) K) i m, (A * S.transpose) i (Fin.castAdd g m) = A i m := by
    intro o A i m
    rw [Matrix.mul_apply, Finset.sum_eq_single m]
    · simp [S]
    · intro b _ hb; simp [S, Matrix.transpose_apply, Ne.symm hb]
    · simp
  have hSn : ∀ {o : Type} (A : Matrix o (Fin g) K) i m, (A * S.transpose) i (Fin.natAdd g m) = 0 := by
    intro o A i m
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [S, Matrix.transpose_apply, Matrix.of_apply, if_neg (hnc m b), mul_zero]
  have hTc : ∀ {o : Type} (A : Matrix o (Fin g) K) i m, (A * T.transpose) i (Fin.castAdd g m) = 0 := by
    intro o A i m
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [T, Matrix.transpose_apply, Matrix.of_apply, if_neg (hcn m b), mul_zero]
  have hTn : ∀ {o : Type} (A : Matrix o (Fin g) K) i m, (A * T.transpose) i (Fin.natAdd g m) = A i m := by
    intro o A i m
    rw [Matrix.mul_apply, Finset.sum_eq_single m]
    · simp [T]
    · intro b _ hb
      have : Fin.natAdd g m ≠ Fin.natAdd g b := fun h => hb ((Fin.natAdd_inj g).1 h).symm
      simp only [T, Matrix.transpose_apply, Matrix.of_apply, if_neg this, mul_zero]
    · simp
  have hMT : M * T = Ji * Lb.transpose * Rv := by
    ext i l; rw [hAT, hRvr]; simp only [M, ConstLat.compl, Matrix.of_apply, Fin.addCases_right]
  have hM'dec : M' = U' * S.transpose + Ji' * L'.transpose * Rv * T.transpose := by
    ext i k
    refine Fin.addCases (fun m => ?_) (fun m => ?_) k
    · rw [Matrix.add_apply, hSc, hTc, add_zero]; simp [M', ConstLat.compl]
    · rw [Matrix.add_apply, hSn, hTn, zero_add, hRvr]; simp only [M', ConstLat.compl, Matrix.of_apply, Fin.addCases_right]

  have hdet0 : M'.det ≠ 0 := fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  have hu' : IsUnit M'.det := isUnit_iff_ne_zero.2 hdet0
  have hM'inv : ∀ {o : Type} (Z : Matrix (Fin (g + g)) o K), M'⁻¹ * (M' * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu', Matrix.one_mul]
  have hM'inv2 : ∀ {o : Type} (Z : Matrix (Fin (g + g)) o K), M' * (M'⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul]
  have hQP : Q * P = 1 := mul_eq_one_comm.1 hPQ
  have hQP' : ∀ {o : Type} (Z : Matrix (Fin (g + g)) o K), Q * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hdB' : IsUnit B'.det := isUnit_iff_ne_zero.2 (by
    rw [Matrix.det_of_upperTriangular hB']; exact Finset.prod_ne_zero_iff.2 fun i _ => hB'0 i)
  have hdBb : IsUnit Bb.det := isUnit_iff_ne_zero.2 (by
    rw [Matrix.det_of_upperTriangular hBb]; exact Finset.prod_ne_zero_iff.2 fun i _ => hBb0 i)
  have hB'inv : ∀ {o : Type} (Z : Matrix (Fin g) o K), B' * (B'⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdB', Matrix.one_mul]
  have hBbinv : ∀ {o : Type} (Z : Matrix (Fin g) o K), Bb * (Bb⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdBb, Matrix.one_mul]
  have hP : ∀ i j, w (P i j) ≤ η⁻¹ := fun i j => (hPQle i j).1
  have hQ : ∀ i j, w (Q i j) ≤ η⁻¹ := fun i j => (hPQle i j).2
  have hit : 1 ≤ η⁻¹ := (one_le_inv₀ hη).2 hη1
  have hit0 : 0 ≤ η⁻¹ := by positivity
  have hinvle : ∀ i j, w (M'⁻¹ i j) ≤ 1 := inv_le w hw M' hM' hdet
  have hUble : ∀ i l, w (Ub i l) ≤ 1 := fun i l => by rw [← hMS, hAS]; exact hM _ _
  have hU'le : ∀ i l, w (U' i l) ≤ 1 := fun i l => by rw [← hM'S, hAS]; exact hM' _ _
  have h3 : ε / η ^ 3 = ε * η⁻¹ ^ 3 := by rw [div_eq_mul_inv, inv_pow]
  have hb1 : 1 * η⁻¹ * ε ≤ ε / η ^ 3 := by
    rw [h3, one_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (le_self_pow₀ hit (by norm_num)) hε
  set C := B'⁻¹ * Bb with hC
  set E₁ := (Ha - Hb) * Bb with hE₁
  have hXS : X * S = S * C - M'⁻¹ * P * E₁ := by
    have h1 : P * Ub = U' * C - P * E₁ := by
      rw [hUb, hU', hC, hE₁, Matrix.sub_mul, Matrix.mul_sub]
      simp only [Matrix.mul_assoc, hB'inv]
      abel
    calc X * S = M'⁻¹ * (P * (M * S)) := by rw [hXd]; simp only [Matrix.mul_assoc]
      _ = M'⁻¹ * (U' * C) - M'⁻¹ * (P * E₁) := by rw [hMS, h1, Matrix.mul_sub]
      _ = S * C - M'⁻¹ * P * E₁ := by rw [← hM'S, Matrix.mul_assoc M', hM'inv, Matrix.mul_assoc]
  have hE₁le : ∀ i m, w (E₁ i m) ≤ ε := by
    intro i m
    have hu : supN w (Hb.mulVec fun k => Bb k m) ≤ 1 := supN_le w zero_le_one fun j => by
      have : (Hb.mulVec fun k => Bb k m) j = Ub j m := by rw [hUb]; rfl
      rw [this]; exact hUble j m
    have := (le_supN w _ i).trans (hag2 _ hu)
    have e : E₁ i m = (Ha.mulVec (fun k => Bb k m) - Hb.mulVec fun k => Bb k m) i := by
      rw [hE₁, Matrix.sub_mul, Matrix.sub_apply, Pi.sub_apply]; rfl
    rw [e]; exact this
  have hL : ∀ i m, w (X i (Fin.castAdd g m) - (S * C) i m) ≤ ε / η ^ 3 := by
    intro i m
    have e : X i (Fin.castAdd g m) - (S * C) i m = -((M'⁻¹ * P * E₁) i m) := by
      rw [← hAS X, hXS, Matrix.sub_apply]; ring
    rw [e, w.map_neg]
    exact (mul_le w hw (M'⁻¹ * P) E₁ (by positivity) hε (mul_le w hw _ _ zero_le_one hit0 hinvle hP) hE₁le i m).trans hb1
  have hSCc : ∀ l m, (S * C) (Fin.castAdd g l) m = C l m := by
    intro l m
    rw [Matrix.mul_apply, Finset.sum_eq_single l]
    · simp [S]
    · intro b _ hb
      have : Fin.castAdd g l ≠ Fin.castAdd g b := fun h => hb (by simpa using h.symm)
      simp only [S, Matrix.of_apply, if_neg this, zero_mul]
    · simp
  have hSCn : ∀ l m, (S * C) (Fin.natAdd g l) m = 0 := by
    intro l m
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun b _ => by simp only [S, Matrix.of_apply, if_neg (hnc l b), zero_mul]

  set D := Bb⁻¹ * B' with hD
  set G := Ha * B' with hG
  set E₂ := (Ha - Hb) * B' with hE₂
  set Y := S.transpose * X * T with hY
  set δ := T.transpose * X * T with hδ
  have hQU : ∀ {o : Type} (Z : Matrix (Fin g) o K), Q * (U' * Z) = G * Z := fun Z => by
    rw [hU', hG]; simp only [Matrix.mul_assoc, hQP']
  have hQU1 : Q * U' = G := by simpa using hQU (1 : Matrix (Fin g) (Fin g) K)
  have hUQ : ∀ {o : Type} (Z : Matrix (Fin (g + g)) o K), U'.transpose * (Q.transpose * Z) = G.transpose * Z :=
    fun Z => by rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hQU1]
  have hJ'' : ∀ {o : Type} (Z : Matrix (Fin (g + g)) o K), Q.transpose * (J * (Q * (Ji' * Z))) = Z := fun Z => by
    have : Q.transpose * J * Q * Ji' * Z = Z := by rw [hJ', Matrix.one_mul]
    simpa only [Matrix.mul_assoc] using this
  have hLU'' : ∀ {o : Type} (Z : Matrix (Fin g) o K), U'.transpose * (L'.transpose * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hLU', Matrix.transpose_one, Matrix.one_mul]
  have hJJi : ∀ {o : Type} (Z : Matrix (Fin (g + g)) o K), J * (Ji * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hLUb : ∀ {o : Type} (Z : Matrix (Fin g) o K), Ub.transpose * (Lb.transpose * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hLU, Matrix.transpose_one, Matrix.one_mul]
  have hHbB : Hb * B' = Ub * D := by rw [hUb, hD]; simp only [Matrix.mul_assoc, hBbinv]
  have hGs : G = Ub * D + E₂ := by rw [hG, hE₂, Matrix.sub_mul, hHbB]; abel
  have h1 : U'.transpose * (Q.transpose * J * Q) * M' * X * T = G.transpose * J * (M * T) := by
    rw [hXd]; simp only [Matrix.mul_assoc, hM'inv2, hQP', hUQ]
  have h2a : U'.transpose * (Q.transpose * J * Q) * M' = G.transpose * J * G * S.transpose + Rv * T.transpose := by
    rw [hM'dec]; simp only [Matrix.mul_add, Matrix.mul_assoc]; rw [hQU, hUQ, hJ'', hLU'']
  have hkey : G.transpose * J * G * Y + Rv * δ = D.transpose * Rv + E₂.transpose * J * (M * T) := by
    have e1 : G.transpose * J * G * Y + Rv * δ = U'.transpose * (Q.transpose * J * Q) * M' * X * T := by
      rw [h2a, hY, hδ]; simp only [Matrix.add_mul, Matrix.mul_assoc]
    have e2 : Ub.transpose * J * (M * T) = Rv := by rw [hMT]; simp only [Matrix.mul_assoc, hJJi, hLUb]
    rw [e1, h1]
    calc G.transpose * J * (M * T) = D.transpose * (Ub.transpose * J * (M * T)) + E₂.transpose * J * (M * T) := by
          rw [hGs, Matrix.transpose_add, Matrix.transpose_mul]; simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [e2]

  have hδe : ∀ l l', δ l l' = X (Fin.natAdd g l) (Fin.natAdd g l') := by intro l l'; rw [hδ, hAT, hTA]
  have hYe : ∀ l l', Y l l' = X (Fin.castAdd g l) (Fin.natAdd g l') := by intro l l'; rw [hY, hAT, hSA]
  have hXle : ∀ i j, w (X i j) ≤ 1 * η⁻¹ * 1 :=
    mul_le w hw (M'⁻¹ * P) M (by positivity) zero_le_one (mul_le w hw _ _ zero_le_one hit0 hinvle hP) hM
  have hYle : ∀ a b, w (Y a b) ≤ 1 * η⁻¹ * 1 := by intro a b; rw [hYe]; exact hXle _ _
  have hGle : ∀ i a, w (G i a) ≤ η⁻¹ := by
    intro i a
    have := mul_le w hw Q U' hit0 zero_le_one hQ hU'le i a
    rwa [hQU1, mul_one] at this
  have hGJG : ∀ a b, w ((G.transpose * J * G) a b) ≤ η⁻¹ * η⁻¹ * ε := by
    intro a b
    rw [bilin_apply]
    exact iso_scale w Ha J hit hε hiso (fun k => B' k a) (fun k => B' k b) (fun j => hGle j a) (fun j => hGle j b)
  have hE₂le : ∀ i m, w (E₂ i m) ≤ η⁻¹ * ε := by
    intro i m
    have := agree_scale w Ha Hb hit hag1 (fun k => B' k m) (fun j => hGle j m) i
    have e : E₂ i m = -((Hb.mulVec (fun k => B' k m) - Ha.mulVec fun k => B' k m) i) := by
      rw [hE₂, Matrix.sub_mul, Matrix.sub_apply, Pi.sub_apply, neg_sub]; rfl
    rw [e, w.map_neg]; exact this
  have hMTle : ∀ i l, w ((M * T) i l) ≤ 1 := by intro i l; rw [hAT]; exact hM _ _
  have hb2 : η⁻¹ * ε * 1 * 1 ≤ ε / η ^ 3 := by
    calc η⁻¹ * ε * 1 * 1 = 1 * η⁻¹ * ε := by ring
      _ ≤ _ := hb1
  have hb3 : η⁻¹ * η⁻¹ * ε * (1 * η⁻¹ * 1) ≤ ε / η ^ 3 := le_of_eq (by rw [h3]; ring)
  have hR : ∀ l l', w (X (Fin.natAdd g l) (Fin.natAdd g l') - D l'.rev l.rev) ≤ ε / η ^ 3 := by
    intro l l'
    have e := congrFun (congrFun hkey l.rev) l'
    rw [Matrix.add_apply, Matrix.add_apply, hRvl, hRvr, Fin.rev_rev, Matrix.transpose_apply, hδe] at e
    have e' : X (Fin.natAdd g l) (Fin.natAdd g l') - D l'.rev l.rev =
        (E₂.transpose * J * (M * T)) l.rev l' - (G.transpose * J * G * Y) l.rev l' := by
      linear_combination e
    rw [e']
    refine sub_le w hw _ _ ?_ ?_
    · exact (mul_le w hw (E₂.transpose * J) (M * T) (by positivity) zero_le_one
        (mul_le w hw _ _ (by positivity) zero_le_one (fun i j => by rw [Matrix.transpose_apply]; exact hE₂le j i) hJle)
        hMTle _ _).trans hb2
    · exact (mul_le w hw _ Y (by positivity) (by positivity) hGJG hYle _ _).trans hb3
  haveI : Invertible B' := Matrix.invertibleOfIsUnitDet B' hdB'
  haveI : Invertible Bb := Matrix.invertibleOfIsUnitDet Bb hdBb
  have hCt : C.BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hB').mul hBb
  have hDt : D.BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hBb).mul hB'
  have hCd : ∀ l, C l l = Bb l l / B' l l := by
    intro l
    rw [eq_div_iff (hB'0 l), mul_comm, ← tri_mul_diag B' C hB' hCt, hC, hB'inv]
  have hDd : ∀ l, D l l = B' l l / Bb l l := by
    intro l
    rw [eq_div_iff (hBb0 l), mul_comm, ← tri_mul_diag Bb D hBb hDt, hD, hBbinv]
  intro i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine ⟨fun j => ?_, ?_⟩
    · refine Fin.addCases (fun m => ?_) (fun m => ?_) j
      · intro hj
        have hml : m < l := by
          have := Fin.lt_def.1 hj; simp only [Fin.val_castAdd] at this; exact Fin.lt_def.2 this
        have := hL (Fin.castAdd g l) m
        rwa [hSCc, hCt hml, sub_zero] at this
      · intro hj
        exfalso
        have := Fin.lt_def.1 hj; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    · rw [Fin.addCases_left]
      have := hL (Fin.castAdd g l) l
      rwa [hSCc, hCd] at this
  · refine ⟨fun j => ?_, ?_⟩
    · refine Fin.addCases (fun m => ?_) (fun m => ?_) j
      · intro _
        have := hL (Fin.natAdd g l) m
        rwa [hSCn, sub_zero] at this
      · intro hj
        have hml : m < l := by
          have := Fin.lt_def.1 hj; simp only [Fin.val_natAdd] at this; exact Fin.lt_def.2 (by omega)
        have := hR l m
        have h0 : D m.rev l.rev = 0 := hDt (Fin.rev_lt_rev.2 hml)
        rwa [h0, sub_zero] at this
    · rw [Fin.addCases_right]
      have := hR l l
      rwa [hDd] at this

end GlobalTheory.FrameCmp
