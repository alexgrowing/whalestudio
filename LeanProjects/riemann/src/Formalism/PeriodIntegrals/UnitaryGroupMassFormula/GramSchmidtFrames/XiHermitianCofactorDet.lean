import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GsFramesOfLoc

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section qrefl

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

def qr (u : Fin m → ℂ) (c : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - c⁻¹ • vecMulVec u (star u ᵥ* H)

lemma vmv_mulVec (u v : Fin m → ℂ) :
    vecMulVec u (star u ᵥ* H) *ᵥ v = herm H v u • u := by
  have e : herm H v u = (star u ᵥ* H) ⬝ᵥ v := by unfold herm; rw [dotProduct_mulVec]
  rw [e]
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma qr_mulVec (u : Fin m → ℂ) (c : ℂ) (v : Fin m → ℂ) :
    qr H u c *ᵥ v = v - (herm H v u / c) • u := by
  rw [qr, sub_mulVec, one_mulVec, smul_mulVec, vmv_mulVec, smul_smul, div_eq_inv_mul]

lemma qr_fix {u v : Fin m → ℂ} (c : ℂ) (h : herm H v u = 0) : qr H u c *ᵥ v = v := by
  rw [qr_mulVec, h, zero_div, zero_smul, sub_zero]

lemma uh_of_herm {g : Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ x y : Fin m → ℂ, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : g ∈ UH H := by
  show gᴴ * H * g = H
  have key : ∀ x y : Fin m → ℂ, herm (gᴴ * H * g) x y = herm H x y := by
    intro x y
    rw [← h x y]
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  ext i j
  have := key (Pi.single j 1) (Pi.single i 1)
  simpa [herm, dotProduct, mulVec, Pi.single_apply] using this

lemma qr_herm (hH : Hᴴ = H) (u : Fin m → ℂ) {c : ℂ} (hc0 : c ≠ 0) (hc : c + star c = herm H u u)
    (x y : Fin m → ℂ) : herm H (qr H u c *ᵥ x) (qr H u c *ᵥ y) = herm H x y := by
  rw [qr_mulVec, qr_mulVec]
  simp only [hm_sub_l, hm_sub_r, hm_smul_l, hm_smul_r]
  rw [hm_symm H hH y u, ← hc, star_div₀]
  have hc1 : star c ≠ 0 := star_ne_zero.2 hc0
  field_simp
  ring

lemma qr_uh (hH : Hᴴ = H) (u : Fin m → ℂ) {c : ℂ} (hc0 : c ≠ 0) (hc : c + star c = herm H u u) :
    qr H u c ∈ UH H := uh_of_herm H (qr_herm H hH u hc0 hc)

lemma uh_mul {g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  calc (g * h)ᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hg', hh']

end qrefl

section hpk

variable {k r : ℕ}

lemma hH_ct : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1

lemma hH_sq : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1

lemma herm_out_wb {v u : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) (hu : inWb k r u) :
    herm (Hpk k r) v u = 0 := by
  unfold herm
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun l _ => ?_)
    by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
    · rw [hv l hl.1 hl.2, mul_zero]
    · have h0 : Hpk k r j l = 0 := by
        simp only [Hpk]
        split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (exfalso; apply hl; rw [← h3.2.2]; exact hj)
      rw [h0, zero_mul]
  · rw [hu j (by omega), star_zero, zero_mul]

lemma herm_wb_out {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u)
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) :
    herm (Hpk k r) u v = 0 := by
  rw [hm_symm _ hH_ct v u, herm_out_wb hv hu, star_zero]

lemma bvec_eI_mid (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → bvec (eI k r a) i = 0 := by
  intro i h1 _
  simp only [bvec, Pi.single_apply]
  rw [if_neg]
  rintro rfl
  have := a.isLt
  simp only [eI, Fin.val_mk] at h1
  omega

lemma bvec_esI_mid (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → bvec (esI k r a) i = 0 := by
  intro i _ h2
  simp only [bvec, Pi.single_apply]
  rw [if_neg]
  rintro rfl
  have := a.isLt
  simp only [esI, Fin.val_mk] at h2
  omega

lemma wbPart_mid (v : Fin (2 * r + k + 1) → ℂ) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → (v - wbPart k r v) i = 0 := by
  intro i h1 h2
  simp only [Pi.sub_apply, wbPart]
  rw [if_pos ⟨h1, h2⟩, sub_self]

lemma wbPart_inWb (v : Fin (2 * r + k + 1) → ℂ) : inWb k r (wbPart k r v) := by
  intro i hi
  simp only [wbPart]
  rw [if_neg (by omega)]

lemma Tz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : (Tz k r z : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 hz.2.ne'

lemma prW_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    prW k r z v ∈ Wsp k r z := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have h0 : wbPart k r v i = 0 := wbPart_inWb v i hi
    simp only [prW, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, hz.1 i hi, mul_zero, add_zero]
  · simp only [prW]
    rw [hm_add_l, hm_smul_l, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, mul_neg, div_mul_cancel₀ _ (Tz_ne hz),
      add_neg_cancel]

lemma herm_prW_r {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) q (prW k r z v) = herm (Hpk k r) q v := by
  have e1 : herm (Hpk k r) q (v - wbPart k r v) = 0 := herm_wb_out hq.1 (wbPart_mid v)
  have e2 : herm (Hpk k r) q z = 0 := hq.2
  simp only [prW]
  rw [hm_add_r, hm_smul_r, e2, mul_zero, add_zero]
  rw [hm_sub_r, sub_eq_zero] at e1
  exact e1.symm

lemma herm_prW_l {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (prW k r z v) q = herm (Hpk k r) v q := by
  rw [hm_symm _ hH_ct q (prW k r z v), herm_prW_r hq]
  exact (hm_symm _ hH_ct q v).symm

lemma esI_hi {ξ : Fin (2 * r + k + 1) → ℂ} (hX : ∀ a : Fin r, ξ (esI k r a) = 0) :
    ∀ i : Fin (2 * r + k + 1), r + k < i.val → ξ i = 0 := by
  intro i hi
  have := i.isLt
  have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i := Fin.ext (by simp only [esI, Fin.val_mk]; omega)
  rw [← e]
  exact hX _

lemma sub_wbPart_X {ξ : Fin (2 * r + k + 1) → ℂ} (hX : ∀ a : Fin r, ξ (esI k r a) = 0) :
    ξ - wbPart k r ξ ∈ Xsp k r := by
  rw [mem_Xsp_iff]
  intro i hi
  by_cases h2 : i.val ≤ r + k
  · exact wbPart_mid ξ i hi h2
  · simp only [Pi.sub_apply, wbPart]
    rw [if_neg (by omega), sub_zero]
    exact esI_hi hX i (by omega)

lemma herm_add_X {p q x x' : Fin (2 * r + k + 1) → ℂ} (hp : inWb k r p) (hq : inWb k r q)
    (hx : x ∈ Xsp k r) (hx' : x' ∈ Xsp k r) :
    herm (Hpk k r) (p + x) (q + x') = herm (Hpk k r) p q := by
  rw [hm_add_l, hm_add_r, hm_add_r, herm_wb_X hx' (wb_hi hp), herm_X_gen hx (wb_hi hq),
    herm_X_gen hx (X_hi hx')]
  simp

lemma fv_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by simp [fvec]

lemma fv_X (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) (hb : b ≠ Fin.last r) : fvec k r z b ∈ Xsp k r := by
  have hb' : b.val < r := by
    have h1 := b.isLt
    have h2 : b.val ≠ r := fun h => hb (Fin.ext (by rw [h, Fin.val_last]))
    omega
  rw [fvec, dif_pos hb']
  exact Submodule.subset_span ⟨⟨b.val, hb'⟩, rfl⟩

lemma fv_hi {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (b : Fin (r + 1)) :
    ∀ i : Fin (2 * r + k + 1), r + k < i.val → fvec k r z b i = 0 := by
  by_cases hb : b = Fin.last r
  · subst hb; rw [fv_last]; exact wb_hi hz
  · exact X_hi (fv_X z b hb)

lemma key_pr {z ξ : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hX : ∀ a : Fin r, ξ (esI k r a) = 0)
    (h0 : prW k r z ξ = 0) :
    herm (Hpk k r) ξ ξ * herm (Hpk k r) z z = herm (Hpk k r) ξ z * star (herm (Hpk k r) ξ z) := by
  have h0' := h0
  unfold prW at h0'
  have hw : wbPart k r ξ = (-(herm (Hpk k r) (wbPart k r ξ) z / (Tz k r z : ℂ))) • z := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0'
  set c := -(herm (Hpk k r) (wbPart k r ξ) z / (Tz k r z : ℂ))
  have hx := sub_wbPart_X hX
  have hξ : ξ = c • z + (ξ - wbPart k r ξ) := by rw [← hw]; abel
  have hcz : inWb k r (c • z) := fun i hi => by simp [hz.1 i hi]
  have e1 : herm (Hpk k r) ξ ξ = herm (Hpk k r) (c • z) (c • z) := by
    conv_lhs => rw [hξ]
    exact herm_add_X hcz hcz hx hx
  have e2 : herm (Hpk k r) ξ z = herm (Hpk k r) (c • z) z := by
    conv_lhs => rw [hξ]
    rw [hm_add_l, herm_X_gen hx (wb_hi hz.1), add_zero]
  rw [e1, e2]
  simp only [hm_smul_l, hm_smul_r, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, star_mul', star_neg, Complex.star_def,
    Complex.conj_ofReal]
  ring

lemma adj_LL (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    M.adjugate (Fin.last r) (Fin.last r) = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [Fin.succAbove_last, ← two_mul]

lemma xcof_self {z z' : Fin (2 * r + k + 1) → ℂ} (hz' : C2.StdZ k r z') {y : B.Mat k r} (hy : y ∈ B.GV k r) :
    herm (Hpk k r) (xcof k r z z' y) (xcof k r z z' y) =
      (Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r) *
        (star ((Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r)) * herm (Hpk k r) z' z') := by
  unfold xcof
  rw [hm_sum_l]
  simp_rw [hm_sum_r, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · rw [fv_last]
    · intro b' _ hb'
      rw [fv_last, herm_wb_X (fv_X z' b' hb') (wb_hi hz'.1), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b' _ => ?_)
    rw [herm_X_gen (fv_X z' b hb) (fv_hi hz'.1 b'), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma herm_Hpk_xcof_eq_det_Zhat (z z' : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r) :
    herm (Hpk k r) (xcof k r z z' y) z = (Zhat k r z z' y).det := by
  unfold xcof
  rw [hm_sum_l]
  have h := congrFun (congrFun (Matrix.mul_adjugate (Zhat k r z z' y)) (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]
  simp only [Zhat, fv_last]

lemma xcofL_self {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (y : B.Mat k r) :
    herm (Hpk k r) (xcofL k r z z' y) (xcofL k r z z' y) =
      star ((Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r)) *
        ((Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r) * herm (Hpk k r) z z) := by
  unfold xcofL
  rw [hm_sum_l]
  simp_rw [hm_sum_r, star_star]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · rw [fv_last]
    · intro b' _ hb'
      rw [fv_last, herm_wb_X (fv_X z b' hb') (wb_hi hz.1), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b' _ => ?_)
    rw [herm_X_gen (fv_X z b hb) (fv_hi hz.1 b'), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma ginv_cancel {y : B.Mat k r} (hy : y ∈ B.GV k r) (v : Fin (2 * r + k + 1) → ℂ) : y *ᵥ (y⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy), one_mulVec]

lemma xi_hermitian_cofactor_det {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hy : y ∈ B.GV k r) :
    herm (Hpk k r) (y⁻¹ *ᵥ xcofL k r z z' y) z' = star (Zhat k r z z' y).det := by
  rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy (y⁻¹ *ᵥ xcofL k r z z' y) z', ginv_cancel hy]
  unfold xcofL
  rw [hm_sum_l]
  have h := congrFun (congrFun (Matrix.adjugate_mul (Zhat k r z z' y)) (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_mul']
  congr 1
  simp only [Zhat, fv_last]
  exact hm_symm _ hH_ct (y *ᵥ z') (fvec k r z a)

lemma omW_ne {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hy : y ∈ B.GV k r) (hG : 0 < Gf k r z z' y) : omW k r z z' y ≠ 0 := by
  intro h0
  have key := key_pr hz (xcof_esI z z' y) h0
  rw [xcof_self hz' hy, herm_Hpk_xcof_eq_det_Zhat, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, adj_LL] at key
  have hG' : 0 < Complex.normSq (Zhat k r z z' y).det -
      Tz k r z * Tz k r z' * Complex.normSq ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det := hG
  set a := ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det
  set d := (Zhat k r z z' y).det
  simp only [Complex.star_def] at key
  have e : ((Complex.normSq a * Tz k r z' * Tz k r z : ℝ) : ℂ) = ((Complex.normSq d : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    linear_combination key
  have e' := Complex.ofReal_injective e
  linarith [e', show Tz k r z * Tz k r z' * Complex.normSq a = Complex.normSq a * Tz k r z' * Tz k r z by ring]

lemma omW'_ne {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hy : y ∈ B.GV k r) (hG : 0 < Gf k r z z' y) : omW' k r z z' y ≠ 0 := by
  intro h0
  have key := key_pr hz' (ginv_xcofL_esI z z' hy) h0
  have hs : herm (Hpk k r) (y⁻¹ *ᵥ xcofL k r z z' y) (y⁻¹ *ᵥ xcofL k r z z' y) =
      herm (Hpk k r) (xcofL k r z z' y) (xcofL k r z z' y) := by
    rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ginv_cancel hy]
  rw [hs, xcofL_self hz, xi_hermitian_cofactor_det hy, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, adj_LL,
    star_star] at key
  have hG' : 0 < Complex.normSq (Zhat k r z z' y).det -
      Tz k r z * Tz k r z' * Complex.normSq ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det := hG
  set a := ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det
  set d := (Zhat k r z z' y).det
  simp only [Complex.star_def] at key
  have e : ((Complex.normSq a * Tz k r z' * Tz k r z : ℝ) : ℂ) = ((Complex.normSq d : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    linear_combination key
  have e' := Complex.ofReal_injective e
  linarith [e', show Tz k r z * Tz k r z' * Complex.normSq a = Complex.normSq a * Tz k r z' * Tz k r z by ring]

end hpk

end PI.UnitaryGroupMassFormula.GsFr
