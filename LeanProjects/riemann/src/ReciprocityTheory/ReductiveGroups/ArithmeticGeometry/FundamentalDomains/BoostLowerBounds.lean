import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RankOneBoostIsometries

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace BoostLowerBounds

open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries

variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}

include hz

private theorem hermC_Gm_add_left (u u' v : Fin r → ℂ) :
    hermC τ.1 X.Gm (u + u') v = hermC τ.1 X.Gm u v + hermC τ.1 X.Gm u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hermC_Gm_sub_left (u u' v : Fin r → ℂ) :
    hermC τ.1 X.Gm (u - u') v = hermC τ.1 X.Gm u v - hermC τ.1 X.Gm u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hermC_Gm_smul_left (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (c • u) v = c * hermC τ.1 X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem hermC_Gm_add_right (u v v' : Fin r → ℂ) :
    hermC τ.1 X.Gm u (v + v') = hermC τ.1 X.Gm u v + hermC τ.1 X.Gm u v' := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private theorem hermC_Gm_sub_right (u v v' : Fin r → ℂ) :
    hermC τ.1 X.Gm u (v - v') = hermC τ.1 X.Gm u v - hermC τ.1 X.Gm u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem hermC_Gm_smul_right (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u (c • v) = conj c * hermC τ.1 X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem hermC_Gm_sum_left {n : ℕ} (f : Fin n → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, f a) v = ∑ a, hermC τ.1 X.Gm (f a) v :=
  map_sum (AddMonoidHom.mk' (fun u => hermC τ.1 X.Gm u v)
    (fun u u' => hermC_Gm_add_left X τ hz u u' v)) f Finset.univ

private theorem det_gramPos_ne_zero : (X.gramPos z τ).det ≠ 0 := by
  have hz' : ∀ ψ : X.Ψ, (mat z ψ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm z ψ i).re := hz
  have h2 := (hz' τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
  have hd : dmin X.Gm z τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos z τ).det := rfl
  intro h0
  rw [hd, h0] at h2
  simp at h2

private theorem hermC_ppos_col_castLE (u : Fin r → ℂ) (k : Fin X.p0) :
    hermC τ.1 X.Gm (X.ppos z τ u) (col (mat z τ) (Fin.castLE X.p0_le k)) =
      hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le k)) := by
  have hinv : (X.gramPos z τ)⁻¹ * X.gramPos z τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_gramPos_ne_zero X τ hz))
  have hgk : ∀ a b : Fin X.p0, hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a))
      (col (mat z τ) (Fin.castLE X.p0_le b)) = X.gramPos z τ a b := fun a b => rfl
  rw [Data.ppos, hermC_Gm_sum_left X τ hz]
  simp only [hermC_Gm_smul_left X τ hz, hgk]
  calc ∑ a, (∑ b, hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le b)) *
          (X.gramPos z τ)⁻¹ b a) * X.gramPos z τ a k
      = ∑ b, hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le b)) *
          ((X.gramPos z τ)⁻¹ * X.gramPos z τ) b k := by
        simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = _ := by
        rw [hinv]
        simp [Matrix.one_apply]

private theorem hermC_ppos_right_eq_sum_gramPos_inv (x w : Fin r → ℂ) :
    hermC τ.1 X.Gm x (X.ppos z τ w) = ∑ a, conj (∑ b, hermC τ.1 X.Gm w
      (col (mat z τ) (Fin.castLE X.p0_le b)) * (X.gramPos z τ)⁻¹ b a) *
        hermC τ.1 X.Gm x (col (mat z τ) (Fin.castLE X.p0_le a)) := by
  rw [← FD.hermC_conj τ.1 X.Gm_herm (X.ppos z τ w) x, Data.ppos, hermC_Gm_sum_left X τ hz, map_sum]
  simp only [hermC_Gm_smul_left X τ hz, map_mul, FD.hermC_conj τ.1 X.Gm_herm]

private theorem hermC_ppos_ppos (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos z τ u) (X.ppos z τ w) = hermC τ.1 X.Gm u (X.ppos z τ w) := by
  rw [hermC_ppos_right_eq_sum_gramPos_inv X τ hz (X.ppos z τ u) w, hermC_ppos_right_eq_sum_gramPos_inv X τ hz u w]
  simp only [hermC_ppos_col_castLE X τ hz]

private theorem hermC_ppos_self_adjoint (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos z τ u) w = hermC τ.1 X.Gm u (X.ppos z τ w) := by
  rw [← FD.hermC_conj τ.1 X.Gm_herm w (X.ppos z τ u), ← hermC_ppos_ppos X τ hz w u,
    FD.hermC_conj τ.1 X.Gm_herm, hermC_ppos_ppos X τ hz u w]

private theorem hermC_jp_left_eq_hermC_jp_right (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp z τ u) w = hermC τ.1 X.Gm u (X.jp z τ w) := by
  simp only [Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_sub_right X τ hz,
    hermC_Gm_smul_right X τ hz, map_ofNat, hermC_ppos_self_adjoint X τ hz]

private theorem hermC_jp_jp' (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp z τ u) (X.jp z τ w) = hermC τ.1 X.Gm u w := by
  simp only [Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_sub_right X τ hz,
    hermC_Gm_smul_right X τ hz, map_ofNat]
  rw [hermC_ppos_ppos X τ hz u w, hermC_ppos_self_adjoint X τ hz u w]
  ring

private theorem ppos_add' (u w : Fin r → ℂ) :
    X.ppos z τ (u + w) = X.ppos z τ u + X.ppos z τ w := by
  simp only [Data.ppos, hermC_Gm_add_left X τ hz, add_mul, Finset.sum_add_distrib, add_smul]

private theorem ppos_smul_eq_smul_ppos (t : ℂ) (u : Fin r → ℂ) :
    X.ppos z τ (t • u) = t • X.ppos z τ u := by
  simp only [Data.ppos, hermC_Gm_smul_left X τ hz, Finset.smul_sum, smul_smul, Finset.mul_sum,
    mul_assoc]

private theorem jp_add' (u w : Fin r → ℂ) :
    X.jp z τ (u + w) = X.jp z τ u + X.jp z τ w := by
  simp only [Data.jp, ppos_add' X τ hz, smul_add]
  abel

private theorem jp_smul' (t : ℂ) (u : Fin r → ℂ) :
    X.jp z τ (t • u) = t • X.jp z τ u := by
  simp only [Data.jp, ppos_smul_eq_smul_ppos X τ hz, smul_sub, smul_smul]
  rw [mul_comm]

private theorem maj_eq_re_hermC_jp (v : Fin r → ℂ) :
    X.maj z τ v = (hermC τ.1 X.Gm (X.jp z τ v) v).re := by
  have h1 : hermC τ.1 X.Gm (X.ppos z τ v) v = ∑ a, ∑ b,
      hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    rw [Data.ppos, hermC_Gm_sum_left X τ hz]
    simp only [hermC_Gm_smul_left X τ hz, FD.hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
    exact Finset.sum_comm
  simp only [Data.maj, Data.posPart, Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, ← h1]
  simp [Complex.sub_re, Complex.mul_re]

private theorem eq_zero_of_hermC_Gm_left_eq_zero (w : Fin r → ℂ) (H : ∀ u, hermC τ.1 X.Gm u w = 0) : w = 0 := by
  have hdet : (X.Gm.map τ.1).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ.1).mpr X.Gm_det
  have hmv : (X.Gm.map τ.1).mulVec (fun b => conj (w b)) = 0 := by
    funext a
    have h := H (Pi.single a 1)
    change (∑ b, (X.Gm.map τ.1) a b * conj (w b)) = 0
    simpa [hermC, Pi.single_apply, Matrix.map_apply] using h
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  funext b
  simpa using congrFun h0 b

private theorem maj_add_smul (v u : Fin r → ℂ) (t : ℂ) :
    X.maj z τ (v + t • u) = X.maj z τ v +
      2 * (conj t * hermC τ.1 X.Gm (X.jp z τ v) u).re + Complex.normSq t * X.maj z τ u := by
  have hs : hermC τ.1 X.Gm (X.jp z τ u) v = conj (hermC τ.1 X.Gm (X.jp z τ v) u) := by
    rw [FD.hermC_conj τ.1 X.Gm_herm, hermC_jp_left_eq_hermC_jp_right X τ hz]
  rw [maj_eq_re_hermC_jp X τ hz (v + t • u), maj_eq_re_hermC_jp X τ hz v, maj_eq_re_hermC_jp X τ hz u,
    jp_add' X τ hz, jp_smul' X τ hz, hermC_Gm_add_left X τ hz, hermC_Gm_smul_left X τ hz,
    hermC_Gm_add_right X τ hz, hermC_Gm_add_right X τ hz, hermC_Gm_smul_right X τ hz, hermC_Gm_smul_right X τ hz, hs]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

private theorem hermC_jp_eq_zero_of_maj_eq_zero (u v : Fin r → ℂ) (hu : X.maj z τ u = 0) :
    hermC τ.1 X.Gm (X.jp z τ v) u = 0 := by
  by_contra hw
  have hn := Complex.normSq_pos.mpr hw
  have h1 := MajorantConjugateTransfer.maj_nonneg (X := X) hz τ
    (v + (-(((X.maj z τ v + 1) / (2 * Complex.normSq (hermC τ.1 X.Gm (X.jp z τ v) u)) : ℝ) : ℂ) *
      hermC τ.1 X.Gm (X.jp z τ v) u) • u)
  rw [maj_add_smul X τ hz, hu, mul_zero, add_zero] at h1
  generalize hW : hermC τ.1 X.Gm (X.jp z τ v) u = W at h1 hn
  generalize hM : X.maj z τ v = M at h1
  have hS : Complex.normSq W ≠ 0 := ne_of_gt hn
  have h2 : (conj (-(((M + 1) / (2 * Complex.normSq W) : ℝ) : ℂ) * W) * W).re =
      -((M + 1) / (2 * Complex.normSq W)) * Complex.normSq W := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have h3 : -((M + 1) / (2 * Complex.normSq W)) * Complex.normSq W = -((M + 1) / 2) := by
    rw [neg_mul, div_mul_eq_mul_div, mul_div_mul_right _ _ hS]
  rw [h2, h3] at h1
  linarith

theorem plane_facts (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) :
    0 < X.maj z τ e ∧ hermC τ.1 X.Gm (X.jp z τ e) (X.jp z τ e) = 0 ∧
      hermC τ.1 X.Gm e (X.jp z τ e) = X.maj z τ e ∧
      hermC τ.1 X.Gm (X.jp z τ e) e = X.maj z τ e := by
  have hre : hermC τ.1 X.Gm (X.jp z τ e) e = X.maj z τ e := by
    rw [maj_eq_re_hermC_jp X τ hz e]
    have hc : conj (hermC τ.1 X.Gm (X.jp z τ e) e) = hermC τ.1 X.Gm (X.jp z τ e) e := by
      rw [FD.hermC_conj τ.1 X.Gm_herm, hermC_jp_left_eq_hermC_jp_right X τ hz]
    exact (Complex.conj_eq_iff_re.mp hc).symm
  have hiso : hermC τ.1 X.Gm (X.jp z τ e) (X.jp z τ e) = 0 := by
    rw [hermC_jp_jp' X τ hz, hee]
  have hsym : hermC τ.1 X.Gm e (X.jp z τ e) = X.maj z τ e := by
    rw [← hermC_jp_left_eq_hermC_jp_right X τ hz, hre]
  have hpos : 0 < X.maj z τ e := by
    rcases (MajorantConjugateTransfer.maj_nonneg (X := X) hz τ e).lt_or_eq with h | h
    · exact h
    · exfalso
      have hje : X.jp z τ e = 0 := eq_zero_of_hermC_Gm_left_eq_zero X τ hz _ fun u => by
        rw [← hermC_jp_left_eq_hermC_jp_right X τ hz u e]
        exact hermC_jp_eq_zero_of_maj_eq_zero X τ hz e u h.symm
      exact he0 (eq_zero_of_hermC_Gm_left_eq_zero X τ hz _ fun u => by
        rw [← hermC_jp_jp' X τ hz u e, hje]
        simp [hermC])
  exact ⟨hpos, hiso, hsym, hre⟩

theorem maj_decomp (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) (w0 : Fin r → ℂ)
    (h0e : hermC τ.1 X.Gm w0 e = 0) (h0f : hermC τ.1 X.Gm w0 (X.jp z τ e) = 0) (a b : ℂ) :
    X.maj z τ (w0 + a • e + b • X.jp z τ e) =
      X.maj z τ w0 + (Complex.normSq a + Complex.normSq b) * X.maj z τ e := by
  obtain ⟨-, hff, -, -⟩ := plane_facts X τ hz hee he0
  have hjw : hermC τ.1 X.Gm (X.jp z τ w0) e = 0 := by
    rw [hermC_jp_left_eq_hermC_jp_right X τ hz, h0f]
  have hjf : hermC τ.1 X.Gm (X.jp z τ (w0 + a • e)) (X.jp z τ e) = 0 := by
    rw [jp_add' X τ hz, jp_smul' X τ hz, hermC_Gm_add_left X τ hz, hermC_Gm_smul_left X τ hz,
      hermC_jp_jp' X τ hz w0 e, h0e, hff, mul_zero, add_zero]
  have hmf : X.maj z τ (X.jp z τ e) = X.maj z τ e := by
    rw [maj_eq_re_hermC_jp X τ hz (X.jp z τ e), maj_eq_re_hermC_jp X τ hz e, hermC_jp_jp' X τ hz (X.jp z τ e) e]
  rw [maj_add_smul X τ hz (w0 + a • e), maj_add_smul X τ hz w0, hjw, hjf, hmf]
  simp only [mul_zero, Complex.zero_re, add_zero]
  ring

theorem boost_lower (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (w : Fin r → ℂ) :
    min (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w ≤
      X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) := by
  obtain ⟨hm, hff, hef, hfe⟩ := plane_facts X τ hz hee he0
  have hm0 : ((X.maj z τ e : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = hermC τ.1 X.Gm w (X.jp z τ e) / (X.maj z τ e : ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = hermC τ.1 X.Gm w e / (X.maj z τ e : ℂ) := ⟨_, rfl⟩
  have hwf : hermC τ.1 X.Gm w (X.jp z τ e) = A * X.maj z τ e := by
    rw [hA, div_mul_cancel₀ _ hm0]
  have hwe : hermC τ.1 X.Gm w e = B * X.maj z τ e := by
    rw [hB, div_mul_cancel₀ _ hm0]
  have h0e : hermC τ.1 X.Gm (w - A • e - B • X.jp z τ e) e = 0 := by
    rw [hermC_Gm_sub_left X τ hz, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_smul_left X τ hz, hee, hfe,
      hwe]
    ring
  have h0f : hermC τ.1 X.Gm (w - A • e - B • X.jp z τ e) (X.jp z τ e) = 0 := by
    rw [hermC_Gm_sub_left X τ hz, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_smul_left X τ hz, hef, hff,
      hwf]
    ring
  have hw : w = (w - A • e - B • X.jp z τ e) + A • e + B • X.jp z τ e := by abel
  have hBw : Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w =
      (w - A • e - B • X.jp z τ e) + ((σ : ℂ)⁻¹ * A) • e + ((σ : ℂ) * B) • X.jp z τ e := by
    rw [boost_mulVec, hwf, hwe]
    have c1 : (((σ⁻¹ - 1) / X.maj z τ e : ℝ) : ℂ) * (A * (X.maj z τ e : ℂ)) =
        (σ : ℂ)⁻¹ * A - A := by
      push_cast
      field_simp
    have c2 : (((σ⁻¹⁻¹ - 1) / X.maj z τ e : ℝ) : ℂ) * (B * (X.maj z τ e : ℂ)) =
        (σ : ℂ) * B - B := by
      rw [inv_inv]
      push_cast
      field_simp
    rw [c1, c2, sub_smul, sub_smul]
    abel
  have hmw : X.maj z τ w = X.maj z τ (w - A • e - B • X.jp z τ e) +
      (Complex.normSq A + Complex.normSq B) * X.maj z τ e := by
    rw [← maj_decomp X τ hz hee he0 _ h0e h0f A B, ← hw]
  rw [hBw, maj_decomp X τ hz hee he0 _ h0e h0f, hmw]
  simp only [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal]
  have hM0 := MajorantConjugateTransfer.maj_nonneg (X := X) hz τ (w - A • e - B • X.jp z τ e)
  have hNA := Complex.normSq_nonneg A
  have hNB := Complex.normSq_nonneg B
  have hs0 : 0 < σ * σ := mul_pos hσ hσ
  rw [sq]
  have hk2 : min (σ * σ) (σ * σ)⁻¹ ≤ σ * σ := min_le_left _ _
  have hk3 : min (σ * σ) (σ * σ)⁻¹ ≤ (σ * σ)⁻¹ := min_le_right _ _
  have hk1 : min (σ * σ) (σ * σ)⁻¹ ≤ 1 := by
    rcases le_total (σ * σ) 1 with h | h
    · exact hk2.trans h
    · refine hk3.trans ?_
      have hi : (σ * σ)⁻¹ * (σ * σ) = 1 := inv_mul_cancel₀ hs0.ne'
      have hip : 0 < (σ * σ)⁻¹ := inv_pos.mpr hs0
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hk1 hM0,
    mul_le_mul_of_nonneg_right hk3 (mul_nonneg hNA hm.le),
    mul_le_mul_of_nonneg_right hk2 (mul_nonneg hNB hm.le)]

end BoostLowerBounds

end ReciprocityTheory.ChartRestriction.G.FD
