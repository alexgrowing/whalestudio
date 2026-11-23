import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.ExpMulVecFix
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace QnYLeibnizW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Gen

variable {n : ℕ}

def evL (w : Fin n → ℂ) (p : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M *ᵥ w) p
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }

lemma evL_apply (w : Fin n → ℂ) (p : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) : evL w p M = (M *ᵥ w) p := rfl

def hermL (H : Matrix (Fin n) (Fin n) ℂ) (w x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => herm H (M *ᵥ w) x
      map_add' := fun M N => by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c M => by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }

lemma hermL_apply (H : Matrix (Fin n) (Fin n) ℂ) (w x : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    hermL H w x M = herm H (M *ᵥ w) x := rfl

lemma curve_zero (g X : Matrix (Fin n) (Fin n) ℂ) :
    g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
  simp [NormedSpace.exp_zero]

lemma rdV_of_hasDerivAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) (L : E)
    (hf : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) L 0) : RdV X f g = L := by
  exact hf.deriv

lemma rdV_smul_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X g : Matrix (Fin n) (Fin n) ℂ) (φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (d : ℂ) (L : E)
    (hφ : HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) d 0)
    (hf : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) L 0) :
    RdV X (fun x => φ x • f x) g = φ g • L + d • f g := by
  apply rdV_of_hasDerivAt
  have h := hφ.smul hf
  simp only [curve_zero] at h
  exact h

lemma single_mulVec_bvec (p s q : Fin n) :
    Matrix.single p s (1 : ℂ) *ᵥ bvec q = if q = s then bvec p else 0 := by
  funext j
  simp only [bvec, Matrix.mulVec_single, Matrix.single_apply, mul_one]
  by_cases h : q = s
  · subst h
    by_cases hj : j = p
    · subst hj
      simp
    · simp [hj, Ne.symm hj, Pi.single_apply]
  · simp [h, Ne.symm h]

lemma single_conjTranspose (p s : Fin n) :
    (Matrix.single p s (1 : ℂ))ᴴ = Matrix.single s p 1 := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  split_ifs <;> first | (exfalso; tauto) | simp

lemma hpart_sum (H Z : Matrix (Fin n) (Fin n) ℂ) : hpart1 H Z + Complex.I • hpart2 H Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [hI, ← smul_add]
  have e : Z - H⁻¹ * Zᴴ * H + (Z + H⁻¹ * Zᴴ * H) = (2 : ℂ) • Z := by
    rw [two_smul]
    abel
  rw [e, smul_smul]
  norm_num

lemma hpart1_skew (H Z : Matrix (Fin n) (Fin n) ℂ) (hHh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 := by
  have hHinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  have hHH' : ∀ X : Matrix (Fin n) (Fin n) ℂ, H * (H * X) = X := fun X => by
    rw [← mul_assoc, hHH, one_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold hpart1
  rw [hHinv, Matrix.conjTranspose_smul, hs, smul_mul_assoc, Matrix.mul_smul, ← smul_add]
  have e : (Z - H * Zᴴ * H)ᴴ * H + H * (Z - H * Zᴴ * H) = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, sub_mul,
      mul_sub, mul_assoc, hHH, hHH', mul_one]
    abel
  rw [e, smul_zero]

lemma hpart2_skew (H Z : Matrix (Fin n) (Fin n) ℂ) (hHh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by
  have hHinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  have hHH' : ∀ X : Matrix (Fin n) (Fin n) ℂ, H * (H * X) = X := fun X => by
    rw [← mul_assoc, hHH, one_mul]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    first | (simp; done) | (simp [mul_neg, inv_neg]; done) | (rw [star_div₀, star_one, star_mul', star_ofNat, Complex.star_def, Complex.conj_I, mul_neg, div_neg])
  unfold hpart2
  rw [hHinv, Matrix.conjTranspose_smul, hs, smul_mul_assoc, Matrix.mul_smul, neg_smul, ← smul_neg, ← smul_add]
  have e : -((Z + H * Zᴴ * H)ᴴ * H) + H * (Z + H * Zᴴ * H) = 0 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, add_mul,
      mul_add, mul_assoc, hHH, hHH', mul_one, neg_add]
    abel
  rw [e, smul_zero]

end Gen

section Pos

variable {k r : ℕ} {i : Fin (r + 1)}

lemma posL_val (j : Fin (mdim k r i)) : (posL k r i j).val = j.val + i.val := rfl

lemma posL_inj (a b : Fin (mdim k r i)) : posL k r i a = posL k r i b ↔ a = b := by
  constructor
  · intro h
    apply Fin.ext
    have h2 := congrArg Fin.val h
    rw [posL_val, posL_val] at h2
    omega
  · rintro rfl
    rfl

lemma out_ne (p : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : q.val < i.val ∨ 2 * r + k < q.val + i.val) :
    q ≠ posL k r i p ∧ q ≠ GBasic.sig k r (posL k r i p) := by
  have hp := p.isLt
  have hi := i.isLt
  unfold mdim at hp
  constructor
  · intro h
    have h2 := congrArg Fin.val h
    rw [posL_val] at h2
    omega
  · intro h
    have h2 := congrArg Fin.val h
    unfold GBasic.sig at h2
    split_ifs at h2 with hc
    · simp only [posL_val] at h2 hc
      omega
    · rw [posL_val] at h2
      omega

lemma hpart_kill (a b : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : q.val < i.val ∨ 2 * r + k < q.val + i.val) :
    hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec q = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec q = 0 := by
  obtain ⟨hqa, _⟩ := out_ne a q hq
  obtain ⟨hqb, _⟩ := out_ne b q hq
  have h1 : Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) *ᵥ bvec q = 0 := by
    rw [single_mulVec_bvec, if_neg hqb]
  have hw : (Hpk k r *ᵥ bvec q) (posL k r i a) = 0 := by
    have ha := a.isLt
    have hi := i.isLt
    unfold mdim at ha
    have hv := posL_val (k := k) (r := r) (i := i) a
    have he : (Hpk k r *ᵥ bvec q) (posL k r i a) = Hpk k r (posL k r i a) q := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [he]
    unfold Hpk
    try beta_reduce
    split_ifs <;> first | rfl | (exfalso; omega) | (exfalso; rw [Fin.ext_iff] at *; omega)
  have h2 : (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ *ᵥ (Hpk k r *ᵥ bvec q) = 0 := by
    rw [single_conjTranspose]
    generalize Hpk k r *ᵥ bvec q = w at hw ⊢
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with hl
    · rw [← hl.2, hw, mul_zero]
    · rw [zero_mul]
  constructor
  · unfold hpart1
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero,
      h1, sub_zero, smul_zero]
  · unfold hpart2
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero,
      h1, add_zero, smul_zero]

lemma hpart_mem (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
      inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := GBasic.Hpk_herm k r
  have hHH : Hpk k r * Hpk k r = 1 := GBasic.Hpk_sq k r
  have hs : ∀ a' : Fin r, a'.val < i.val → (esI k r a').val < i.val ∨ 2 * r + k < (esI k r a').val + i.val := by
    intro a' ha'
    right
    have := a'.isLt
    show 2 * r + k < 2 * r + k - a'.val + i.val
    omega
  have he : ∀ a' : Fin r, a'.val < i.val → (eI k r a').val < i.val ∨ 2 * r + k < (eI k r a').val + i.val :=
    fun a' ha' => Or.inl ha'
  constructor
  · unfold inLieLev
    exact ⟨hpart1_skew _ _ hH hHH, fun a' ha' => ⟨(hpart_kill a b _ (he a' ha')).1, (hpart_kill a b _ (hs a' ha')).1⟩⟩
  · unfold inLieLev
    exact ⟨hpart2_skew _ _ hH hHH, fun a' ha' => ⟨(hpart_kill a b _ (he a' ha')).2, (hpart_kill a b _ (hs a' ha')).2⟩⟩

end Pos

section Deriv

variable {k r : ℕ} {i : Fin (r + 1)}

private theorem hasDerivAt_mul_exp_smul_zero' {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  let large₂ : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => g * M
      map_add' := fun M N => Matrix.mul_add g M N
      map_smul' := fun c M => by simp [Matrix.mul_smul] }
  have h := large₂.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_matrix_exp_smul_at_zero X)
  exact h

lemma hasDerivAt_f {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f F : Mx k r → E) (U : Set (Mx k r)) (g X : Mx k r) (hU : IsOpen U) (hgU : g ∈ U)
    (hg : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ Glev k r i → f h = F h)
    (hX : inLieLev k r i X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := hasDerivAt_mul_exp_smul_zero' g X
  have hFd : DifferentiableAt ℝ F g :=
    (hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by first | simp | exact_mod_cast le_top)
  have h1 := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (curve_zero g X).symm
  apply h1.congr_of_eventuallyEq
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U := by
    have hmem : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
      rw [curve_zero]
      exact hU.mem_nhds hgU
    exact hc.continuousAt.preimage_mem_nhds hmem
  filter_upwards [hev] with t ht
  exact hfF _ ht (glev_mul hg (exp_mem_glev hX t))

lemma hasDerivAt_yv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) (g X : Mx k r) :
    HasDerivAt (fun t : ℝ => yv k r z i (g * NormedSpace.exp ((t : ℂ) • X)) c)
      (-((X *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))) 0 := by
  have hfun : (fun t : ℝ => yv k r z i (g * NormedSpace.exp ((t : ℂ) • X)) c) =
      fun t : ℝ => evL (g⁻¹ *ᵥ fvec k r z i) (posL k r i c) (NormedSpace.exp ((t : ℂ) • (-X))) := by
    funext t
    show ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ fvec k r z i) (posL k r i c) =
      (NormedSpace.exp ((t : ℂ) • (-X)) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c)
    rw [Matrix.mulVec_mulVec, smul_neg, Matrix.exp_neg, ← Matrix.mul_inv_rev]
  rw [hfun]
  have h := (evL (g⁻¹ *ᵥ fvec k r z i) (posL k r i c)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_matrix_exp_smul_at_zero (-X))
  refine h.congr_deriv ?_
  show ((-X) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c) = -((X *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))
  rw [Matrix.neg_mulVec]
  rfl

lemma hasDerivAt_ybv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) (g X : Mx k r) :
    HasDerivAt (fun t : ℝ => ybv k r z i (g * NormedSpace.exp ((t : ℂ) • X)) c)
      (herm (Hpk k r) ((g * X) *ᵥ bvec (posL k r i c)) (fvec k r z i)) 0 := by
  have h := (hermL (Hpk k r) (bvec (posL k r i c)) (fvec k r z i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_mul_exp_smul_zero' g X)
  exact h

end Deriv

theorem y_operator_leibniz_rule : YLeibniz := by
  unfold YLeibniz
  intro E _ _ k r z i D a b c f hD hf g hg
  obtain ⟨hgG, hgD⟩ := hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g ⟨hgG, hgD⟩
  have hmem := hpart_mem (k := k) (r := r) (i := i) a b
  have hf1 := hasDerivAt_f f F U g (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) hU hgU hgG hF hfF hmem.1
  have hf2 := hasDerivAt_f f F U g (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) hU hgU hgG hF hfF hmem.2
  have L1 : RdV (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) f g = fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := rdV_of_hasDerivAt _ g f _ hf1
  have L2 : RdV (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) f g = fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := rdV_of_hasDerivAt _ g f _ hf2
  have eEH : ∀ h : Mx k r → E, EH k r (posL k r i a) (posL k r i b) h g =
      RdV (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) h g + Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) h g := fun h => rfl
  have e1 : ∀ (s d1 d2 : ℂ) (M1 M2 v : E), s • M1 + d1 • v + Complex.I • (s • M2 + d2 • v) =
      s • (M1 + Complex.I • M2) + (d1 + Complex.I * d2) • v := by
    intro s d1 d2 M1 M2 v
    simp only [smul_add, add_smul, mul_smul]
    rw [smul_comm Complex.I s M2]
    abel
  have hsum : (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) + Complex.I • hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) = Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) := hpart_sum _ _
  constructor
  · have R1 : RdV (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun x => yv k r z i x c • f x) g =
        yv k r z i g c • fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) + (-((hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))) • f g :=
      rdV_smul_of _ g (fun x => yv k r z i x c) f _ _ (hasDerivAt_yv z c g _) hf1
    have R2 : RdV (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun x => yv k r z i x c • f x) g =
        yv k r z i g c • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) + (-((hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))) • f g :=
      rdV_smul_of _ g (fun x => yv k r z i x c) f _ _ (hasDerivAt_yv z c g _) hf2
    have hZw : (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c) = if a = c then yv k r z i g b else 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
      by_cases hac : a = c
      · subst hac
        simp [yv, Matrix.mulVec, dotProduct]
      · have hne : posL k r i a ≠ posL k r i c := fun h => hac ((posL_inj a c).mp h)
        simp [hne, hac]
    have key1 : (-((hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))) + Complex.I * (-((hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))) =
        -(if a = c then yv k r z i g b else 0) := by
      have hc : ((hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) + Complex.I • hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c) =
          (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c) + Complex.I * (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c) := by
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum, hZw] at hc
      rw [hc]
      ring
    rw [eEH, eEH, R1, R2, L1, L2, e1, key1, neg_smul, ← sub_eq_add_neg, ite_smul, zero_smul]
  · have R1 : RdV (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun x => ybv k r z i x c • f x) g =
        ybv k r z i g c • fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) +
          herm (Hpk k r) ((g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ bvec (posL k r i c)) (fvec k r z i) • f g :=
      rdV_smul_of _ g (fun x => ybv k r z i x c) f _ _ (hasDerivAt_ybv z c g _) hf1
    have R2 : RdV (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun x => ybv k r z i x c • f x) g =
        ybv k r z i g c • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) +
          herm (Hpk k r) ((g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ bvec (posL k r i c)) (fvec k r z i) • f g :=
      rdV_smul_of _ g (fun x => ybv k r z i x c) f _ _ (hasDerivAt_ybv z c g _) hf2
    have hlin : ∀ u v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) u (fvec k r z i) + Complex.I * herm (Hpk k r) v (fvec k r z i) =
        herm (Hpk k r) (u + Complex.I • v) (fvec k r z i) := by
      intro u v
      simp only [herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hv : g *ᵥ ((hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) + Complex.I • hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ bvec (posL k r i c)) =
        (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ bvec (posL k r i c) + Complex.I • ((g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ bvec (posL k r i c)) := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec]
    rw [hsum] at hv
    have key2 : herm (Hpk k r) ((g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ bvec (posL k r i c)) (fvec k r z i) +
        Complex.I * herm (Hpk k r) ((g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) *ᵥ bvec (posL k r i c)) (fvec k r z i) =
        if b = c then ybv k r z i g a else 0 := by
      rw [hlin, ← hv, single_mulVec_bvec]
      by_cases hbc : b = c
      · subst hbc
        rw [if_pos rfl, if_pos rfl]
        rfl
      · rw [if_neg (fun h => hbc ((posL_inj c b).mp h).symm), if_neg hbc, Matrix.mulVec_zero]
        simp [herm]
    rw [eEH, eEH, R1, R2, L1, L2, e1, key2, ite_smul, zero_smul]

end QnYLeibnizW
