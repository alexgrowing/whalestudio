import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStep

open Matrix

noncomputable section

namespace PI.StabPairsW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

def sgI (k r : ℕ) (i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

lemma hpk_apply (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l.val = sgI k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, sgI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma sgI_lt (i : Fin (2 * r + k + 1)) : sgI k r i.val < 2 * r + k + 1 := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> omega

lemma sgI_sgI (i : Fin (2 * r + k + 1)) : sgI k r (sgI k r i.val) = i.val := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> omega

lemma sgI_eq_iff (i : Fin (2 * r + k + 1)) : sgI k r i.val = r + k ↔ i.val = r + k := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> constructor <;> intro <;> omega

theorem hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [hpk_apply]
  rw [Finset.sum_eq_single (⟨sgI k r i.val, sgI_lt i⟩ : Fin (2 * r + k + 1))]
  · simp only [if_true, sgI_sgI]
    by_cases hil : i = l
    · subst hil
      by_cases hi : i.val = r + k
      · have h2 : sgI k r (r + k) = r + k := hi ▸ (sgI_eq_iff i).2 hi
        simp [hi, h2]
      · have h2 : ¬ sgI k r i.val = r + k := fun h => hi ((sgI_eq_iff i).1 h)
        simp [hi, h2]
    · have h3 : ¬ l.val = i.val := fun h => hil (Fin.ext h.symm)
      simp [h3, hil]
  · intro j _ hj
    have h4 : ¬ j.val = sgI k r i.val := fun h => hj (Fin.ext h)
    simp [h4]
  · simp

theorem hpk_det_ne : (Hpk k r).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hpk_mul_self (k := k) (r := r))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by
  ext i l
  rw [Matrix.conjTranspose_apply, hpk_apply, hpk_apply]
  by_cases h : i.val = sgI k r l.val
  · have h' : l.val = sgI k r i.val := by rw [h, sgI_sgI]
    have hs : (i.val = r + k ↔ l.val = r + k) := by rw [h, sgI_eq_iff]
    rw [if_pos h, if_pos h']
    by_cases hl : l.val = r + k
    · simp [hl, hs.2 hl]
    · have hi : ¬ i.val = r + k := fun h2 => hl (hs.1 h2)
      simp [hl, hi]
  · have h' : ¬ l.val = sgI k r i.val := fun h' => h (by rw [h', sgI_sgI])
    rw [if_neg h, if_neg h']
    simp

theorem mem_GV_iff {g : B.Mat k r} : g ∈ B.GV k r ↔ gᴴ * Hpk k r * g = Hpk k r := Iff.rfl

theorem mul_mem_GV {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) : a * b ∈ B.GV k r := by
  rw [mem_GV_iff] at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha, hb]

theorem det_ne_of_mem_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) : g.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (mem_GV_iff.1 hg)
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  exact hpk_det_ne h1.symm

theorem isUnit_det_of_mem_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) : IsUnit g.det :=
  isUnit_iff_ne_zero.2 (det_ne_of_mem_GV hg)

theorem inv_mem_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r := by
  have hu := isUnit_det_of_mem_GV hg
  rw [mem_GV_iff] at *
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu]
        simp

def Ff (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r z a i

theorem Fm_eq (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Fm k r z z' γ = Matrix.fromCols (Ff k r z) (γ * Ff k r z') := by
  ext i j
  cases j <;> simp [Fm, Ff, gramVec, Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem Fm_conjTranspose (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (Fm k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by
  ext i j
  simp [Fm, Matrix.conjTranspose_apply]

theorem mem_Uperp_iff (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ Uperp k r z z' γ ↔ ((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  rw [Fm_conjTranspose]
  rfl

private lemma conjTranspose_mul_mul_apply_eq_dotProduct {p q : Type} [Fintype p] [Fintype q]
    (A : Matrix (Fin (2 * r + k + 1)) p ℂ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (C : Matrix (Fin (2 * r + k + 1)) q ℂ) (i : p) (j : q) :
    (Aᴴ * M * C) i j = star (fun l => A l i) ⬝ᵥ (M *ᵥ fun l => C l j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Pi.star_apply]

theorem gramM_eq (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    gramM k r z z' γ = (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
  ext i j
  rw [conjTranspose_mul_mul_apply_eq_dotProduct]
  rfl

theorem Zhat_eq (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Zhat k r z z' γ = (Ff k r z)ᴴ * Hpk k r * γ * Ff k r z' := by
  ext a b
  rw [show (Ff k r z)ᴴ * Hpk k r * γ * Ff k r z' = (Ff k r z)ᴴ * Hpk k r * (γ * Ff k r z') by
    simp only [Matrix.mul_assoc], conjTranspose_mul_mul_apply_eq_dotProduct]
  have h1 : (fun l => (γ * Ff k r z') l b) = γ *ᵥ fvec k r z' b := by
    funext l
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ff]
  rw [h1]
  rfl

theorem herm_swap (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [Matrix.dotProduct_mulVec, Matrix.star_dotProduct, Matrix.star_mulVec, star_star,
    hpk_conjTranspose]

theorem herm_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    mem_GV_iff.1 hg]

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) j = (if j.val = r + k then -1 else 1) * v ⟨sgI k r j.val, sgI_lt j⟩ := by
  rw [Matrix.mulVec, dotProduct]
  simp_rw [hpk_apply]
  rw [Finset.sum_eq_single (⟨sgI k r j.val, sgI_lt j⟩ : Fin (2 * r + k + 1))]
  · simp
  · intro l _ hl
    have h4 : ¬ l.val = sgI k r j.val := fun h => hl (Fin.ext h)
    simp [h4]
  · simp

theorem herm_bvec (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec j) = (Hpk k r *ᵥ v) j := by
  simp [herm, bvec, dotProduct, Pi.single_apply]

theorem herm_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  have ha := a.isLt
  rw [herm_bvec, hpk_mulVec]
  have h1 : ¬ (eI k r a).val = r + k := by simp [eI]; omega
  rw [if_neg h1, one_mul]
  congr 1
  ext
  simp [eI, esI, sgI, ha]

theorem herm_es (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  rw [herm_bvec, hpk_mulVec]
  have h1 : ¬ (esI k r a).val = r + k := by simp [esI]; omega
  rw [if_neg h1, one_mul]
  have h2 : sgI k r (2 * r + k - a.val) = a.val := by
    unfold sgI
    rw [if_pos (Or.inr (by omega))]
    omega
  congr 1
  ext
  simp [esI, eI, h2]

theorem bvec_apply (i j : Fin (2 * r + k + 1)) : bvec i j = if j = i then 1 else 0 := by
  simp [bvec, Pi.single_apply]

theorem herm_sum_left (v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ a, c a • v a) w = ∑ a, c a * herm (Hpk k r) (v a) w := by
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  simp [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fvec_eI (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    fvec k r z c (eI k r a) = if c.val = a.val then 1 else 0 := by
  have ha := a.isLt
  have hc := c.isLt
  unfold fvec
  by_cases h : c.val < r
  · rw [dif_pos h]
    simp only [bvec, Pi.single_apply, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [dif_neg h, hz (eI k r a) (Or.inl (by simp [eI])), if_neg (by omega)]

theorem z_esI (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a : Fin r) : z (esI k r a) = 0 :=
  hz (esI k r a) (Or.inr (by have := a.isLt; simp [esI]; omega))

theorem fvec_esI (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    fvec k r z c (esI k r a) = 0 := by
  have ha := a.isLt
  unfold fvec
  by_cases h : c.val < r
  · rw [dif_pos h]
    simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff]
    rw [if_neg (by omega)]
  · rw [dif_neg h]
    exact z_esI z hz a

theorem herm_Hpk_fvec_eq_ite (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c = Fin.last r then herm (Hpk k r) z z else 0 := by
  by_cases hc : c.val < r
  · have hne : c ≠ Fin.last r := fun h => by rw [h] at hc; simp at hc
    rw [if_neg hne]
    simp only [fvec, dif_pos hc]
    rw [herm_swap, herm_e, z_esI z hz]
    simp
  · have heq : c = Fin.last r := Fin.ext (by have := c.isLt; simp; omega)
    rw [if_pos heq]
    simp only [fvec, dif_neg hc]

theorem herm_fvec_fvec (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) =
      if a = Fin.last r ∧ b = Fin.last r then herm (Hpk k r) z z else 0 := by
  by_cases ha : a.val < r
  · have hne : a ≠ Fin.last r := fun h => by rw [h] at ha; simp at ha
    rw [if_neg (fun h => hne h.1)]
    rw [show fvec k r z a = bvec (eI k r ⟨a.val, ha⟩) by simp [fvec, ha], herm_e, fvec_esI z hz]
  · have heq : a = Fin.last r := Fin.ext (by have := a.isLt; simp; omega)
    rw [show fvec k r z a = z by simp [fvec, ha], herm_Hpk_fvec_eq_ite z hz b]
    simp [heq]

theorem herm_self_re (v : Fin (2 * r + k + 1) → ℂ) :
    ((herm (Hpk k r) v v).re : ℂ) = herm (Hpk k r) v v := by
  have h := herm_swap (k := k) (r := r) v v
  exact Complex.conj_eq_iff_re.1 h.symm

theorem Adiag_apply (z : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    Adiag k r z a b = if a = Fin.last r ∧ b = Fin.last r then herm (Hpk k r) z z else 0 := by
  simp only [Adiag, Matrix.diagonal_apply, Tz, Complex.ofReal_neg, neg_neg, herm_self_re]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = Fin.last r <;> simp [ha]
  · rw [if_neg hab]
    have h2 : ¬ (a = Fin.last r ∧ b = Fin.last r) := fun h => hab (h.1.trans h.2.symm)
    rw [if_neg h2]

theorem gramM_blocks (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (γ : B.Mat k r)
    (hγ : γ ∈ B.GV k r) :
    gramM k r z z' γ = Matrix.fromBlocks (Adiag k r z) (Zhat k r z z' γ) (Zhat k r z z' γ)ᴴ (Adiag k r z') := by
  ext (a | a) (b | b)
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    rw [herm_fvec_fvec z hz, Adiag_apply]
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [herm_swap]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [herm_GV hγ, herm_fvec_fvec z' hz', Adiag_apply]

theorem det_Zhat_ne (z z' : Fin (2 * r + k + 1) → ℂ) (hS : Std k r z z') (γ : B.Mat k r) (hP : PosPt k r z z' γ) :
    (Zhat k r z z' γ).det ≠ 0 := by
  intro h0
  obtain ⟨_, ⟨_, hT⟩, ⟨_, hT'⟩⟩ := hS
  obtain ⟨_, hG⟩ := hP
  have hD : Dmin k r z z' γ (Fin.last (r + 1)) = 0 := by
    unfold Dmin
    have h1 : (Zhat k r z z' γ).submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt)) = Zhat k r z z' γ := by
      ext i j
      rfl
    rw [h1]
    exact h0
  unfold Gf at hG
  rw [hD, Complex.normSq_zero, zero_sub] at hG
  have h2 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' γ ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hT.le hT'.le) (Complex.normSq_nonneg _)
  linarith

theorem col_of_mul (z : Fin (2 * r + k + 1) → ℂ) (s : B.Mat k r) (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (h : s * Ff k r z = Ff k r z * x) (b : Fin (r + 1)) : s *ᵥ fvec k r z b = ∑ c, x c b • fvec k r z c := by
  funext i
  have h1 := congrFun (congrFun h i) b
  simp only [Matrix.mul_apply, Ff, Matrix.of_apply] at h1
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem uMap_eq (z : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z) (s : B.Mat k r)
    (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (h : s * Ff k r z = Ff k r z * x) : uMap k r z s = x := by
  obtain ⟨hzW, hT⟩ := hz
  ext a b
  have hcol := col_of_mul z s x h b
  simp only [uMap]
  split_ifs with ha
  · rw [hcol, herm_sum_left]
    simp_rw [herm_es, fvec_eI z hzW]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      have h2 : ¬ c.val = a.val := fun h2 => hc (Fin.ext h2)
      simp [h2]
    · simp
  · have heq : a = Fin.last r := Fin.ext (by have := a.isLt; simp; omega)
    have hne : herm (Hpk k r) z z ≠ 0 := by
      intro h0
      simp [Tz, h0] at hT
    rw [hcol, herm_sum_left]
    simp_rw [herm_Hpk_fvec_eq_ite z hzW]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [if_pos rfl, heq, mul_div_assoc, div_self hne, mul_one]
    · intro c _ hc
      rw [if_neg hc, mul_zero]
    · simp

end PI.StabPairsW
