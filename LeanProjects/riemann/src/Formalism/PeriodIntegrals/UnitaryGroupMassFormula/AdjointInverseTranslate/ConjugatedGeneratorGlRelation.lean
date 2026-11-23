import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.SmoothLinear

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def EcH {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (H Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (hpart1 H Z) f g + Complex.I • RdV (hpart2 H Z) f g

section Ec

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ana_rdBracket (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {X Y g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : inLH H X) (hY : inLH H Y) (hg : inUH H g) :
    RdV X (RdV Y f) g - RdV Y (RdV X f) g = RdV (X * Y - Y * X) f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inLH H Z → ∀ k ∈ U, inUH H k → RdV Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkH => rd_extension_h n H E f F U k Z hH hU hk hkH hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H' := (hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H']
    exact add_comm _ _
  have e1 : RdV X (RdV Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    rd_extension_h n H E (RdV Y f) _ U g X hH hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : RdV Y (RdV X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    rd_extension_h n H E (RdV X f) _ U g Y hH hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (ana_bracket hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

lemma ana_Ec_sub (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hg : inUH H g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcH H (Z - W) f g = EcH H Z f g - EcH H W f g := by
  unfold EcH
  rw [ana_hpart1_sub hH, ana_hpart2_sub hH,
    ana_rdSub hH hf (ana_hpartMem hH Z).1 (ana_hpartMem hH W).1 hg,
    ana_rdSub hH hf (ana_hpartMem hH Z).2.1 (ana_hpartMem hH W).2.1 hg, smul_sub]
  abel

lemma ana_Ec_zero (H : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : EcH H 0 f g = 0 := by
  unfold EcH RdV hpart1 hpart2
  simp

lemma ana_EcComm (hH : HInvol H) (f : Matrix (Fin n) (Fin n) ℂ → E) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnH H f) (hg : inUH H g) :
    EcH H Z (EcH H W f) g - EcH H W (EcH H Z f) g = EcH H (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2, hZ, -⟩ := ana_hpartMem hH Z
  obtain ⟨hY1, hY2, hW, -⟩ := ana_hpartMem hH W
  have hEc : ∀ (Z' : Matrix (Fin n) (Fin n) ℂ) (f' : Matrix (Fin n) (Fin n) ℂ → E),
      EcH H Z' f' g = RdV (hpart1 H Z') f' g + Complex.I • RdV (hpart2 H Z') f' g := fun _ _ => rfl
  have hE : ∀ V, inLH H V → ∀ W' : Matrix (Fin n) (Fin n) ℂ,
      RdV V (EcH H W' f) g = RdV V (RdV (hpart1 H W') f) g + Complex.I • RdV V (RdV (hpart2 H W') f) g :=
    fun V hV W' => ana_rdLin hH Complex.I (ana_rdSmooth hH hf (ana_hpartMem hH W').1)
      (ana_rdSmooth hH hf (ana_hpartMem hH W').2.1) hV hg
  have hZW := commutator_complex_expand (hpart1 H Z) (hpart2 H Z) (hpart1 H W) (hpart2 H W)
  rw [← hZ, ← hW] at hZW
  have hP := ana_sub (ana_bracket hX1 hY1) (ana_bracket hX2 hY2)
  have hQ := ana_add (ana_bracket hX1 hY2) (ana_bracket hX2 hY1)
  obtain ⟨h1, h2⟩ := ana_hpart_unique hH hP hQ
  rw [hEc Z, hEc W, hE _ hX1, hE _ hX2, hE _ hY1, hE _ hY2, hZW, hEc, h1, h2,
    ana_rdSub hH hf (ana_bracket hX1 hY1) (ana_bracket hX2 hY2) hg,
    ana_rdAdd hH hf (ana_bracket hX1 hY2) (ana_bracket hX2 hY1) hg,
    ← ana_rdBracket hH hf hX1 hY1 hg, ← ana_rdBracket hH hf hX2 hY2 hg,
    ← ana_rdBracket hH hf hX1 hY2 hg, ← ana_rdBracket hH hf hX2 hY1 hg]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  abel

end Ec

theorem conjugated_generator_gl_relation : EabHGl := by
  unfold EabHGl
  intro n H E _ _ f a b c d g hH hf hg
  have hE : ∀ (i j : Fin n) (φ : Matrix (Fin n) (Fin n) ℂ → E),
      EabH H i j φ = EcH H (Matrix.single i j (1 : ℂ)) φ := fun _ _ _ => rfl
  have hm : ∀ (i j k l : Fin n), Matrix.single i j (1 : ℂ) * Matrix.single k l 1 =
      if j = k then Matrix.single i l 1 else 0 := by
    intro i j k l
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      first
      | rw [Matrix.single_mul_single_same, mul_one]
      | (ext p q; simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'])
    · rw [if_neg hjk]
      first
      | exact Matrix.single_mul_single_of_ne hjk _ _
      | (ext p q; simp [Matrix.mul_apply, Matrix.single_apply, ite_and, hjk, Finset.sum_ite_eq,
          Finset.sum_ite_eq'])
  simp only [hE]
  rw [ana_EcComm hH f _ _ g hf hg, ana_Ec_sub hH hf hg, hm, hm]
  split_ifs <;> simp [ana_Ec_zero]

section Right

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ana_unitInv (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s) : s⁻¹ = H * sᴴ * H := by
  unfold inUH at hs
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc sᴴ, hs, hH.2]

lemma ana_inv_mul (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s) : s⁻¹ * s = 1 := by
  rw [ana_unitInv hH hs]
  unfold inUH at hs
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc sᴴ, hs, hH.2]

lemma ana_mul_inv (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s) : s * s⁻¹ = 1 := by
  first
  | exact Matrix.mul_nonsing_inv s (Matrix.isUnit_det_of_left_inverse (ana_inv_mul hH hs))
  | exact mul_eq_one_comm.1 (ana_inv_mul hH hs)

lemma isUnit_of_inUH (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s) : IsUnit s := ⟨⟨s, s⁻¹, ana_mul_inv hH hs, ana_inv_mul hH hs⟩, rfl⟩

lemma ana_rdRight (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {X s g : Matrix (Fin n) (Fin n) ℂ}
    (hs : inUH H s) : RdV X (fun x => f (x * s)) g = RdV (s⁻¹ * X * s) f (g * s) := by
  unfold RdV
  congr 1
  funext t
  dsimp only
  congr 1
  rw [show ((t : ℂ) • (s⁻¹ * X * s)) = s⁻¹ * ((t : ℂ) • X) * s by rw [Matrix.mul_smul, Matrix.smul_mul],
    Matrix.exp_conj' s _ (isUnit_of_inUH hH hs)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc s s⁻¹, ana_mul_inv hH hs, Matrix.one_mul]

lemma ana_conj_hpart1 (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s)
    (Z : Matrix (Fin n) (Fin n) ℂ) : s⁻¹ * hpart1 H Z * s = hpart1 H (s⁻¹ * Z * s) := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  rw [ana_unitInv hH hs]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.1, Matrix.mul_assoc, ana_HH_left hH,
    hH.2, Matrix.mul_one]

lemma ana_conj_hpart2 (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s)
    (Z : Matrix (Fin n) (Fin n) ℂ) : s⁻¹ * hpart2 H Z * s = hpart2 H (s⁻¹ * Z * s) := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  rw [ana_unitInv hH hs]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.1, Matrix.mul_assoc, ana_HH_left hH,
    hH.2, Matrix.mul_one]

lemma ana_EcH_ext (hH : HInvol H) {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    {g : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hgU : g ∈ U) (hg : inUH H g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUH H h → f h = F h) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcH H Z f g = fderiv ℝ F g (g * hpart1 H Z) + Complex.I • fderiv ℝ F g (g * hpart2 H Z) := by
  unfold EcH
  rw [rd_extension_h n H E f F U g _ hH hU hgU hg hF hfF (ana_hpartMem hH Z).1,
    rd_extension_h n H E f F U g _ hH hU hgU hg hF hfF (ana_hpartMem hH Z).2.1]

lemma ana_Phi_add (hH : HInvol H) (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) (g Z W : Matrix (Fin n) (Fin n) ℂ) :
    L (g * hpart1 H (Z + W)) + Complex.I • L (g * hpart2 H (Z + W)) =
      (L (g * hpart1 H Z) + Complex.I • L (g * hpart2 H Z)) +
        (L (g * hpart1 H W) + Complex.I • L (g * hpart2 H W)) := by
  rw [ana_hpart1_add hH, ana_hpart2_add hH, Matrix.mul_add, Matrix.mul_add, map_add, map_add, smul_add]
  abel

lemma ana_Phi_smul (hH : HInvol H) (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) (g Z : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) :
    L (g * hpart1 H (c • Z)) + Complex.I • L (g * hpart2 H (c • Z)) =
      c • (L (g * hpart1 H Z) + Complex.I • L (g * hpart2 H Z)) := by
  have hr : ∀ (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ), L ((r : ℂ) • M) = (r : ℂ) • L M := by
    intro r M
    rw [show ((r : ℂ) • M) = r • M from Matrix.ext fun i j => by simp [Complex.real_smul], L.map_smul]
    exact (Complex.coe_smul r (L M)).symm
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, c = x + y * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  rw [ana_hpart1_smul hH, ana_hpart2_smul hH, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_smul, map_sub, map_add, hr, hr, hr, hr]
  match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf

def anaPhi (hH : HInvol H) (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E where
  toFun Z := L (g * hpart1 H Z) + Complex.I • L (g * hpart2 H Z)
  map_add' Z W := ana_Phi_add hH L g Z W
  map_smul' c Z := ana_Phi_smul hH L g Z c

lemma ana_conj_single (s : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    s⁻¹ * Matrix.single a b (1 : ℂ) * s = ∑ c, ∑ d, (s⁻¹ c a * s b d) • Matrix.single c d (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq'] <;> ring

end Right

theorem eab_h_right : EabHRight := by
  intro n H E _ _ f a b s g hH hf hs hg
  have hgs := ana_mul hg hs
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g * s) hgs
  change EcH H (Matrix.single a b 1) (fun x => f (x * s)) g =
    ∑ c, ∑ d, (s⁻¹ c a * s b d) • EcH H (Matrix.single c d 1) f (g * s)
  have h1 : EcH H (Matrix.single a b 1) (fun x => f (x * s)) g =
      EcH H (s⁻¹ * Matrix.single a b 1 * s) f (g * s) := by
    unfold EcH
    rw [ana_rdRight hH hs, ana_rdRight hH hs, ana_conj_hpart1 hH hs, ana_conj_hpart2 hH hs]
  rw [h1]
  simp only [ana_EcH_ext hH hU hgU hgs hF hfF]
  change anaPhi hH (fderiv ℝ F (g * s)) (g * s) (s⁻¹ * Matrix.single a b 1 * s) =
    ∑ c, ∑ d, (s⁻¹ c a * s b d) • anaPhi hH (fderiv ℝ F (g * s)) (g * s) (Matrix.single c d 1)
  rw [ana_conj_single, map_sum]
  simp only [map_sum, map_smul]

end AAInvW
