import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDefs

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k r : ℕ}

lemma Hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)

lemma Hb_sq (k : ℕ) : Hb k * Hb k = 1 := by
  unfold Formalism.QuantumDeterminants.Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

private lemma Em_conjTranspose_eq_transpose : (Em k r)ᴴ = (Em k r)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]
  split_ifs <;> simp

private lemma Em_transpose_conjTranspose_eq_Em : ((Em k r)ᵀ)ᴴ = Em k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]
  split_ifs <;> simp

lemma embed_conj_transpose (X : Mb k) : (e0 k r X)ᴴ = e0 k r Xᴴ := by
  unfold Dc.e0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjTranspose_eq_transpose, Em_transpose_conjTranspose_eq_Em]
  simp only [Matrix.mul_assoc]

private lemma Hpk_apply_wI_right_eq_ite (i : Fin (2 * r + k + 1)) (m : Fin (k + 1)) :
    Hpk k r i (wI k r m) = if i = wI k r m then Hb k m m else 0 := by
  have hm := m.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply_eq, wI, Fin.ext_iff, Fin.val_mk, Fin.val_last]
  split_ifs <;> first | rfl | omega | (exfalso; omega)

private lemma Hpk_wI_apply_left_eq_ite (j : Fin (2 * r + k + 1)) (m : Fin (k + 1)) :
    Hpk k r (wI k r m) j = if j = wI k r m then Hb k m m else 0 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  rw [← hH, Matrix.conjTranspose_apply, Hpk_apply_wI_right_eq_ite]
  by_cases h : j = wI k r m
  · simp only [h, if_true, Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [h]

private lemma Hpk_mul_Em_eq_Em_mul_Hb : Hpk k r * Em k r = Em k r * Hb k := by
  ext i m
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single (wI k r m) (fun j _ hj => by simp [Em, hj]) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single m (fun j _ hj => by simp [Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply, hj])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Em, Hpk_apply_wI_right_eq_ite]
  split_ifs <;> simp_all

lemma Hpk_mulVec_e0 (X : Mb k) : Hpk k r * e0 k r X = e0 k r (Hb k * X) := by
  unfold Dc.e0
  simp only [← Matrix.mul_assoc, Hpk_mul_Em_eq_Em_mul_Hb]

private lemma Em_transpose_mul_Hpk_eq_Hb_mul_transpose : (Em k r)ᵀ * Hpk k r = Hb k * (Em k r)ᵀ := by
  ext m i
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single (wI k r m) (fun j _ hj => by simp [Em, hj]) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single m (fun j _ hj => by simp [Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply, Ne.symm hj])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Matrix.transpose_apply, Em, Hpk_wI_apply_left_eq_ite]
  split_ifs <;> simp_all

lemma embed_mul_hermitian_form (X : Mb k) : e0 k r X * Hpk k r = e0 k r (X * Hb k) := by
  unfold Dc.e0
  simp only [Matrix.mul_assoc, Em_transpose_mul_Hpk_eq_Hb_mul_transpose]

lemma embed_add (X Y : Mb k) : e0 k r (X + Y) = e0 k r X + e0 k r Y := by
  unfold Dc.e0
  simp only [Matrix.mul_add, Matrix.add_mul]

lemma embed_sub (X Y : Mb k) : e0 k r (X - Y) = e0 k r X - e0 k r Y := by
  unfold Dc.e0
  simp only [Matrix.mul_sub, Matrix.sub_mul]

lemma embed_smul (c : ℂ) (X : Mb k) : e0 k r (c • X) = c • e0 k r X := by
  unfold Dc.e0
  simp only [Matrix.mul_smul, Matrix.smul_mul]

lemma embed_zero : e0 k r (0 : Mb k) = 0 := by
  unfold Dc.e0
  simp only [Matrix.mul_zero, Matrix.zero_mul]

lemma hermitian_real_part_embed (X : Mb k) :
    hpart1 (Hpk k r) (e0 k r X) = e0 k r ((1 / 2 : ℂ) • (X - Hb k * Xᴴ * Hb k)) := by
  unfold Formalism.QuantumDeterminants.hpart1
  rw [Hpk_inv, embed_conj_transpose, Hpk_mulVec_e0, embed_mul_hermitian_form, embed_smul, embed_sub]

lemma hermitian_imag_part_embed (X : Mb k) :
    hpart2 (Hpk k r) (e0 k r X) = e0 k r ((1 / (2 * Complex.I) : ℂ) • (X + Hb k * Xᴴ * Hb k)) := by
  unfold Formalism.QuantumDeterminants.hpart2
  rw [Hpk_inv, embed_conj_transpose, Hpk_mulVec_e0, embed_mul_hermitian_form, embed_smul, embed_add]

lemma embed_mul_vec (Y : Mb k) (v : Fin (2 * r + k + 1) → ℂ) :
    e0 k r Y *ᵥ v = Em k r *ᵥ (Y *ᵥ ((Em k r)ᵀ *ᵥ v)) := by
  unfold Dc.e0
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma EmT_mulVec (v : Fin (2 * r + k + 1) → ℂ) : (Em k r)ᵀ *ᵥ v = wbPart k r v := by
  ext j
  simp [Matrix.mulVec, dotProduct, Em, wbPart]

lemma wbPart_e (a : Fin r) : wbPart k r (bvec (eI k r a)) = 0 := by
  funext j
  have ha := a.isLt
  simp only [wbPart, bvec, Pi.zero_apply]
  rw [Pi.single_eq_of_ne]
  intro h
  simp only [wI, eI, Fin.ext_iff, Fin.val_mk] at h
  omega

lemma wbPart_es (a : Fin r) : wbPart k r (bvec (esI k r a)) = 0 := by
  funext j
  have ha := a.isLt
  have hj := j.isLt
  simp only [wbPart, bvec, Pi.zero_apply]
  rw [Pi.single_eq_of_ne]
  intro h
  simp only [wI, esI, Fin.ext_iff, Fin.val_mk] at h
  omega

lemma embed_mem_unitary_lie_algebra (z : Fin (2 * r + k + 1) → ℂ) (Y : Mb k) (hY : Yᴴ * Hb k + Hb k * Y = 0)
    (hz : Y *ᵥ wbPart k r z = 0) : P.QrD.InLieW k r z (e0 k r Y) := by
  unfold Formalism.FourierDecayAlt.P.QrD.InLieW Formalism.FourierDecayAlt.Q.inLieLev
  refine ⟨⟨?_, fun a _ => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [embed_conj_transpose, embed_mul_hermitian_form, Hpk_mulVec_e0, ← embed_add, hY, embed_zero]
  · rw [embed_mul_vec, EmT_mulVec, wbPart_e, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · rw [embed_mul_vec, EmT_mulVec, wbPart_es, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · rw [embed_mul_vec, EmT_mulVec, hz, Matrix.mulVec_zero]

lemma skew1 (X : Mb k) :
    ((1 / 2 : ℂ) • (X - Hb k * Xᴴ * Hb k))ᴴ * Hb k + Hb k * ((1 / 2 : ℂ) • (X - Hb k * Xᴴ * Hb k)) = 0 := by
  have h1 : Hb k * Hb k = 1 := Hb_sq k
  have h1' : ∀ Y : Mb k, Hb k * (Hb k * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2 : (Hb k)ᴴ = Hb k := Formalism.FourierDecayAlt.P.SettingConstruction.Hb_herm k
  have h3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have key : (X - Hb k * Xᴴ * Hb k)ᴴ * Hb k + Hb k * (X - Hb k * Xᴴ * Hb k) = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h1, h1', Matrix.mul_one]
    abel
  rw [Matrix.conjTranspose_smul, h3, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, key, smul_zero]

lemma skew2 (X : Mb k) :
    ((1 / (2 * Complex.I) : ℂ) • (X + Hb k * Xᴴ * Hb k))ᴴ * Hb k +
      Hb k * ((1 / (2 * Complex.I) : ℂ) • (X + Hb k * Xᴴ * Hb k)) = 0 := by
  have h1 : Hb k * Hb k = 1 := Hb_sq k
  have h1' : ∀ Y : Mb k, Hb k * (Hb k * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2 : (Hb k)ᴴ = Hb k := Formalism.FourierDecayAlt.P.SettingConstruction.Hb_herm k
  have h3 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    show (starRingEnd ℂ) (1 / (2 * Complex.I)) = _
    rw [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have key : (X + Hb k * Xᴴ * Hb k)ᴴ * Hb k = Hb k * (X + Hb k * Xᴴ * Hb k) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h1, h1', Matrix.mul_one]
    abel
  rw [Matrix.conjTranspose_smul, h3, Matrix.smul_mul, Matrix.mul_smul, key, neg_smul, neg_add_cancel]

lemma gwc_of (z : Fin (2 * r + k + 1) → ℂ) (X : Mb k) (h1 : X *ᵥ wbPart k r z = 0)
    (h2 : (Hb k * Xᴴ * Hb k) *ᵥ wbPart k r z = 0) : GWc k r z (e0 k r X) := by
  have hs : ∀ (c : ℂ) (A : Mb k) (w : Fin (k + 1) → ℂ), (c • A) *ᵥ w = c • (A *ᵥ w) := fun c A w => by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.GWc
  rw [hermitian_real_part_embed, hermitian_imag_part_embed]
  refine ⟨embed_mem_unitary_lie_algebra z _ (skew1 X) ?_, embed_mem_unitary_lie_algebra z _ (skew2 X) ?_⟩
  · rw [hs, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
  · rw [hs, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]

lemma inL_col {C : Mb k} (hC : InL k C) : C *ᵥ Pi.single (Fin.last k) 1 = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, (hC i).1]

lemma inL_colH {C : Mb k} (hC : InL k C) : Cᴴ *ᵥ Pi.single (Fin.last k) 1 = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.conjTranspose_apply, (hC i).2]

lemma Hb_last (k : ℕ) : Hb k *ᵥ Pi.single (Fin.last k) 1 = -Pi.single (Fin.last k) 1 := by
  funext i
  unfold Formalism.QuantumDeterminants.Hb
  rw [Matrix.mulVec_diagonal]
  by_cases h : i = Fin.last k
  · subst h; simp
  · simp [h]

lemma unit_inv {g : Mb k} (hg : gᴴ * Hb k * g = Hb k) : g⁻¹ = Hb k * gᴴ * Hb k := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Hb_sq]

lemma unit_invH {g : Mb k} (hg : gᴴ * Hb k * g = Hb k) : (g⁻¹)ᴴ = Hb k * g * Hb k := by
  have h2 : (Hb k)ᴴ = Hb k := Formalism.FourierDecayAlt.P.SettingConstruction.Hb_herm k
  rw [unit_inv hg]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2, Matrix.mul_assoc]

lemma unit_inv_mul {g : Mb k} (hg : gᴴ * Hb k * g = Hb k) : g⁻¹ * g = 1 := by
  rw [unit_inv hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Hb_sq]

lemma kill_right {g C : Mb k} (hg : gᴴ * Hb k * g = Hb k) (hC : InL k C) {v : Fin (k + 1) → ℂ} {c : ℂ}
    (hv : g *ᵥ v = c • Pi.single (Fin.last k) 1) :
    (g⁻¹ * C * g) *ᵥ v = 0 ∧ (Hb k * (g⁻¹ * C * g)ᴴ * Hb k) *ᵥ v = 0 := by
  have hbb : ∀ w, Hb k *ᵥ (Hb k *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Hb_sq, Matrix.one_mulVec]
  constructor
  · simp only [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, inL_col hC, smul_zero, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, unit_invH hg]
    simp only [← Matrix.mulVec_mulVec, hbb, hv, Matrix.mulVec_smul, Matrix.mulVec_neg, Hb_last, inL_colH hC, neg_zero,
      smul_zero, Matrix.mulVec_zero]

lemma kill_left {g C : Mb k} (hg : gᴴ * Hb k * g = Hb k) (hC : InL k C) {v : Fin (k + 1) → ℂ} {c : ℂ}
    (hv : g *ᵥ (c • Pi.single (Fin.last k) 1) = v) :
    (g * C * g⁻¹) *ᵥ v = 0 ∧ (Hb k * (g * C * g⁻¹)ᴴ * Hb k) *ᵥ v = 0 := by
  subst hv
  have hgg : ∀ w, g⁻¹ *ᵥ (g *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, unit_inv_mul hg, Matrix.one_mulVec]
  have hgg2 : ∀ w, gᴴ *ᵥ (Hb k *ᵥ (g *ᵥ w)) = Hb k *ᵥ w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]
  constructor
  · simp only [← Matrix.mulVec_mulVec, hgg, Matrix.mulVec_smul, inL_col hC, smul_zero, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, unit_invH hg]
    simp only [← Matrix.mulVec_mulVec, hgg2, Matrix.mulVec_smul, Matrix.mulVec_neg, Hb_last, inL_colH hC, neg_zero,
      smul_zero, Matrix.mulVec_zero]

theorem gwc_right (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hT' : 0 < Tz k r z') (C : Mb k)
    (hC : InL k C) :
    GWc k r z' (e0 k r ((gB k (wbPart k r z') (Tz k r z'))⁻¹ * C * gB k (wbPart k r z') (Tz k r z'))) := by
  obtain ⟨hg, hv⟩ := Formalism.FourierDecayAlt.P.TheSec.gB_spec (k := k) hT' (Formalism.FourierDecayAlt.P.SettingConstruction.herm_self (k := k) (r := r) z' hz')
  obtain ⟨h1, h2⟩ := kill_right hg hC hv
  exact gwc_of z' _ h1 h2

theorem gwc_left (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) (C : Mb k)
    (hC : InL k C) :
    GWc k r z (e0 k r (gA k (wbPart k r z) (Tz k r z) * C * (gA k (wbPart k r z) (Tz k r z))⁻¹)) := by
  obtain ⟨hg, hv⟩ := Formalism.FourierDecayAlt.P.TheSec.gA_spec (k := k) hT (Formalism.FourierDecayAlt.P.SettingConstruction.herm_self (k := k) (r := r) z hz)
  obtain ⟨h1, h2⟩ := kill_left hg hC hv
  exact gwc_of z _ h1 h2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
