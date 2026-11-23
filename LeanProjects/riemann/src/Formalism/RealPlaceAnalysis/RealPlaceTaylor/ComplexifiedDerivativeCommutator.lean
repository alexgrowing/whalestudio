import Formalism.RealPlaceAnalysis.SmoothOnG

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def mulRightRealCLM {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

lemma mulRightCLM_apply {n : ℕ} (X h : Matrix (Fin n) (Fin n) ℂ) : mulRightRealCLM X h = h * X := rfl

lemma withTop_enat_infty_add_one_le_infty : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp

theorem rdSmooth_of (h : RdExt) : RdSmooth := by
  intro n ε f X hf hX g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkJ
    exact h n ε f F U k X hU hk hkJ hF hfF hX

lemma lie_algebra_bracket_mem {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hY : inG ε Y) : inG ε (X * Y - Y * X) := by
  unfold inG at *
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * Jm ε = Jm ε * Y * X := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * Jm ε = Jm ε * X * Y := by
    rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
    Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  abel

theorem rdBracket_of (h : RdExt) (hs : RdSmooth) : RdBracket := by
  intro n ε f X Y g hf hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → Rd Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => h n ε f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : Rd X (Rd Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    h n ε (Rd Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : Rd Y (Rd X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    h n ε (Rd X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g := hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

lemma lie_algebra_add_mem_matrix {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A + B) := by
  unfold inG at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * Jm ε + Bᴴ * Jm ε + (Jm ε * A + Jm ε * B)
      = (Aᴴ * Jm ε + Jm ε * A) + (Bᴴ * Jm ε + Jm ε * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

lemma lie_algebra_neg_mem {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) : inG ε (-A) := by
  unfold inG at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]

lemma lie_algebra_sub_mem {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A - B) := by
  rw [sub_eq_add_neg]; exact lie_algebra_add_mem_matrix hA (lie_algebra_neg_mem hB)

lemma lie_algebra_signature_conj {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

lemma complex_parts_unique {n : ℕ} {ε : Fin n → Bool} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : inG ε P) (hQ : inG ε Q) :
    cpart1 ε (P + Complex.I • Q) = P ∧ cpart2 ε (P + Complex.I • Q) = Q := by
  have hZ : Jm ε * (P + Complex.I • Q)ᴴ * Jm ε = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, lie_algebra_signature_conj hP, lie_algebra_signature_conj hQ, Complex.star_def, Complex.conj_I]
    module
  unfold cpart1 cpart2
  rw [hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]

lemma real_part_sub {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Z - W) = cpart1 ε Z - cpart1 ε W := by
  unfold cpart1
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma imaginary_part_sub {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Z - W) = cpart2 ε Z - cpart2 ε W := by
  unfold cpart2
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma commutator_complex_expand {n : ℕ} (X1 X2 Y1 Y2 : Matrix (Fin n) (Fin n) ℂ) :
    (X1 + Complex.I • X2) * (Y1 + Complex.I • Y2) - (Y1 + Complex.I • Y2) * (X1 + Complex.I • X2) =
      ((X1 * Y1 - Y1 * X1) - (X2 * Y2 - Y2 * X2)) +
        Complex.I • ((X1 * Y2 - Y2 * X1) + (X2 * Y1 - Y1 * X2)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq

lemma right_derivative_neg (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hB : inG ε B) (hg : inUJ ε g) :
    Rd (-B) f g = -Rd B f g := by
  have := (hl n ε f f B B (-1) 0 g hf hf hB hB hg).2.1
  have e : (((-1 : ℝ) : ℂ) • B) = -B := by simp
  rw [e] at this
  rw [this]; simp

lemma right_derivative_add (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A + B) f g = Rd A f g + Rd B f g :=
  (hl n ε f f A B 0 0 g hf hf hA hB hg).1

lemma right_derivative_sub (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A - B) f g = Rd A f g - Rd B f g := by
  rw [sub_eq_add_neg, right_derivative_add hl hf hA (lie_algebra_neg_mem hB) hg, right_derivative_neg hl hf hB hg, sub_eq_add_neg]

lemma complexified_derivative_sub (hc : CpartMem) (hl : RdLin) {n : ℕ} {ε : Fin n → Bool}
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f)
    (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    Ec ε (Z - W) f g = Ec ε Z f g - Ec ε W f g := by
  obtain ⟨hZ1, hZ2, -, -⟩ := hc n ε Z
  obtain ⟨hW1, hW2, -, -⟩ := hc n ε W
  unfold Ec
  rw [real_part_sub, imaginary_part_sub, right_derivative_sub hl hf hZ1 hW1 hg, right_derivative_sub hl hf hZ2 hW2 hg]
  ring

lemma complexified_derivative_zero {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : Ec ε 0 f g = 0 := by
  simp [Ec, cpart1, cpart2, Rd]

lemma complexified_derivative_commutator (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) {n : ℕ}
    (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Ec ε Z (Ec ε W f) g - Ec ε W (Ec ε Z f) g = Ec ε (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2, hZ, -⟩ := hc n ε Z
  obtain ⟨hY1, hY2, hW, -⟩ := hc n ε W
  have hEc : ∀ (Z' : Matrix (Fin n) (Fin n) ℂ) (f' : Matrix (Fin n) (Fin n) ℂ → ℂ),
      Ec ε Z' f' g = Rd (cpart1 ε Z') f' g + Complex.I * Rd (cpart2 ε Z') f' g := fun _ _ => rfl
  have hE : ∀ V, inG ε V → ∀ W' : Matrix (Fin n) (Fin n) ℂ,
      Rd V (Ec ε W' f) g = Rd V (Rd (cpart1 ε W') f) g + Complex.I * Rd V (Rd (cpart2 ε W') f) g :=
    fun V hV W' => (hl n ε _ _ V V 0 Complex.I g (hs n ε f _ hf (hc n ε W').1)
      (hs n ε f _ hf (hc n ε W').2.1) hV hV hg).2.2
  have hZW := commutator_complex_expand (cpart1 ε Z) (cpart2 ε Z) (cpart1 ε W) (cpart2 ε W)
  rw [← hZ, ← hW] at hZW
  have hP := lie_algebra_sub_mem (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2)
  have hQ := lie_algebra_add_mem_matrix (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1)
  obtain ⟨h1, h2⟩ := complex_parts_unique hP hQ
  rw [hEc Z, hEc W, hE _ hX1, hE _ hX2, hE _ hY1, hE _ hY2, hZW, hEc, h1, h2,
    right_derivative_sub hl hf (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2) hg,
    right_derivative_add hl hf (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1) hg,
    ← hb n ε f _ _ g hf hX1 hY1 hg, ← hb n ε f _ _ g hf hX2 hY2 hg,
    ← hb n ε f _ _ g hf hX1 hY2 hg, ← hb n ε f _ _ g hf hX2 hY1 hg]
  linear_combination (Rd (cpart2 ε Z) (Rd (cpart2 ε W) f) g -
    Rd (cpart2 ε W) (Rd (cpart2 ε Z) f) g) * Complex.I_mul_I

theorem eabGl_of (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) : EabGl := by
  intro n ε f a b c d g hf hg
  unfold Eab
  rw [complexified_derivative_commutator hc hl hb hs ε f _ _ g hf hg]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  rw [hm, complexified_derivative_sub hc hl hf hg]
  split_ifs <;> simp [complexified_derivative_zero]

end Formalism.REAL
