import Mathlib
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgNorm

open Formalism.FourierDecayAlt.P.Dx2.DF

section form

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem form_add_left (u v w : Fin m → ℂ) : herm H (u + v) w = herm H u w + herm H v w := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem form_add_right (u v w : Fin m → ℂ) : herm H w (u + v) = herm H w u + herm H w v := by
  simp only [herm, star_add, add_dotProduct]

theorem form_sub_left (u v w : Fin m → ℂ) : herm H (u - v) w = herm H u w - herm H v w := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem form_sub_right (u v w : Fin m → ℂ) : herm H w (u - v) = herm H w u - herm H w v := by
  simp only [herm, star_sub, sub_dotProduct]

theorem form_smul_left (c : ℂ) (u w : Fin m → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_smul_right (c : ℂ) (u w : Fin m → ℂ) : herm H w (c • u) = star c * herm H w u := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

end form

variable {k r : ℕ}

theorem inWb_Wb (v : Fin (2 * r + k + 1) → ℂ) : inWb k r (Wb v) := by
  intro i hi
  show (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) = 0
  rw [if_neg (by omega)]

theorem split_of_free {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    v = (∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v := by
  funext i
  have hval : ∀ a : Fin r, (eI k r a).val = a.val := fun a => rfl
  have hsum : (∑ a : Fin r, v (eI k r a) • ee k r a) i = if i.val < r then v i else 0 := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, ee, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · have hi : i = eI k r ⟨i.val, h⟩ := Fin.ext (hval ⟨i.val, h⟩).symm
      rw [Finset.sum_eq_single ⟨i.val, h⟩]
      · rw [if_pos hi, ← hi]
      · intro b _ hb
        rw [if_neg]
        intro hib
        apply hb
        apply Fin.ext
        show b.val = i.val
        rw [hib, hval]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hib
      apply h
      rw [hib, hval]
      exact b.isLt
  rw [Pi.add_apply, hsum]
  show v i = (if i.val < r then v i else 0) + (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0)
  have hlt := i.isLt
  by_cases h1 : i.val < r
  · rw [if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : i.val ≤ r + k
    · rw [if_pos ⟨by omega, h2⟩]
    · rw [if_neg (by omega)]
      have hi : i = esI k r ⟨2 * r + k - i.val, by omega⟩ :=
        Fin.ext (by show i.val = 2 * r + k - (2 * r + k - i.val); omega)
      rw [hi]
      exact hv _

theorem form_Wb_right {v w : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) (hw : inWb k r w) :
    herm (Hpk k r) (Wb v) w = herm (Hpk k r) v w := by
  conv_rhs => rw [split_of_free hv]
  rw [form_add_left, herm_sum_left]
  simp only [form_smul_left, h_ee_w hw, mul_zero, Finset.sum_const_zero, zero_add]

theorem form_Wb_self {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    herm (Hpk k r) (Wb v) (Wb v) = herm (Hpk k r) v v := by
  rw [form_Wb_right hv (inWb_Wb v)]
  have hs := split_of_free hv
  calc herm (Hpk k r) v (Wb v)
      = herm (Hpk k r) v ((∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v) := by
        rw [form_add_right, herm_sum_right]
        simp [form_smul_right, herm_ee, hv]
    _ = herm (Hpk k r) v v := by rw [← hs]

theorem mul_adj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  exact mul_eq_one_comm.mp hl

theorem adj_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r) = Dmin k r z z' g ⟨r, by omega⟩ := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have hs : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hs, one_mul]
  rfl

theorem det_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).det = Dmin k r z z' g (Fin.last (r + 1)) := by
  show _ = Matrix.det ((Zhat k r z z' g).submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl))
  rw [Fin.castLE_rfl, Matrix.submatrix_id_id]

private theorem herm_adjoint_mulVec_eq (g : Mx k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ x) y = herm (Hpk k r) x (g *ᵥ y) := by
  unfold herm
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.one_mul,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem omg_norm : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g : Mx k r), inWb k r z → 0 < Tz k r z →
    inWb k r z' → 0 < Tz k r z' → g ∈ UH (Hpk k r) →
    inWb k r (GlobalTheory.WigSh.omg k r z z' g) ∧ herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) z' = 0 ∧
      (herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) (GlobalTheory.WigSh.omg k r z z' g)).re = Gf k r z z' g / Tz k r z' := by
  intro k r z z' g hz _ hz' hT' hg
  have hTne : (Tz k r z' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hss : herm (Hpk k r) z' z' = -((Tz k r z' : ℝ) : ℂ) := herm_self_alt
  have hsz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := herm_self_alt
  have hs0 : herm (Hpk k r) z' z' ≠ 0 := by rw [hss]; exact neg_ne_zero.mpr hTne
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 * r + k + 1) → ℂ,
      u = ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin (2 * r + k + 1) → ℂ, v = (Hpk k r * gᴴ * Hpk k r) *ᵥ u := ⟨_, rfl⟩
  have homg : GlobalTheory.WigSh.omg k r z z' g = Formalism.FourierDecayAlt.D.prW k r z' v := by
    rw [hv, hu]; rfl
  have hkey : ∀ b : Fin (r + 1), herm (Hpk k r) v (fvec k r z' b) =
      star ((Zhat k r z z' g).det * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.last r) b) := by
    intro b
    have hsym : ∀ a, herm (Hpk k r) (fvec k r z a) (g *ᵥ fvec k r z' b) = star (Zhat k r z z' g a b) := by
      intro a
      rw [herm_symm']
      rfl
    rw [hv, herm_adjoint_mulVec_eq, hu, herm_sum_left]
    simp only [form_smul_left, hsym, ← star_mul', ← star_sum]
    rw [← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hfree : ∀ a : Fin r, v (esI k r a) = 0 := by
    intro a
    rw [← herm_ee v a, ← fvec_cs z' a, hkey, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne', mul_zero,
      star_zero]
  have hlast : ∀ w : Fin (2 * r + k + 1) → ℂ, fvec k r w (Fin.last r) = w := by
    intro w
    simp [fvec]
  have hvz' : herm (Hpk k r) v z' = star (Zhat k r z z' g).det := by
    have h := hkey (Fin.last r)
    rw [hlast, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hWv : herm (Hpk k r) (Wb v) z' = star (Zhat k r z z' g).det := by
    rw [form_Wb_right hfree hz', hvz']
  have hWW : herm (Hpk k r) (Wb v) (Wb v) =
      star ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) *
        ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) * herm (Hpk k r) z z := by
    rw [form_Wb_self hfree, hv, herm_adjoint_mulVec_eq, mulVec_mulVec, mul_adj hg, one_mulVec, hu,
      Fin.sum_univ_castSucc]
    simp only [fvec_cs, hlast]
    simp [herm_sum_left, herm_sum_right, form_add_left, form_add_right, form_smul_left, form_smul_right,
      h_ee_w hz, h_w_ee hz]
    ring
  rw [homg, prW_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [Pi.sub_apply, Pi.smul_apply, inWb_Wb v i hi, hz' i hi, smul_zero, sub_zero]
  · rw [form_sub_left, form_smul_left, div_mul_cancel₀ _ hs0, sub_self]
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, herm_symm' (Wb v) z', hWv, hWW, hss, hsz]
    unfold Gf
    rw [← det_last, ← adj_last]
    set d := (Zhat k r z z' g).det
    set A := (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)
    have hT'0 : Tz k r z' ≠ 0 := hT'.ne'
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_conj]
    simp only [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.div_im, Complex.neg_im,
      Complex.normSq_neg, Complex.normSq_ofReal]
    field_simp
    ring

end GlobalTheory.WigSh.OmgNorm
