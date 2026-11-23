import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem vector_right_derivative_extends : RdExtV := by
  intro n ε E _ _ f F U g X hU hg hgJ hF hfF hX
  unfold RdV
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (indefinite_unitary_mul_mem ε hgJ (exp_indefinite_unitary_holds n ε X hX t))
  rw [hev.deriv_eq]
  exact hcomp.deriv

theorem vector_right_derivative_left_invariant : RdLeftV := by
  intro n E _ _ f X h g
  simp only [RdV, mul_assoc]

theorem rdSmoothV_of (h : RdExtV) : RdSmoothV := by
  intro n ε E _ _ f X hf hX g0 hg0
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  obtain ⟨U, F, hU, hg0U, hF, hfF⟩ := hf g0 hg0
  refine ⟨U, fun x => fderiv ℝ F x (x * X), hU, hg0U, ?_,
    fun x hx hxJ => h n ε E f F U x X hU hx hxJ hF hfF hX⟩
  have hF1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hF).2
  have hL : ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y * X) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff
  exact hF1.clm_apply hL.contDiffOn

private lemma inG_add_real_place_taylor {m : ℕ} {e : Fin m → Bool} {X Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : inG e X) (hY : inG e Y) : inG e (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem rdLinV_of (h : RdExtV) : RdLinV := by
  intro n ε E _ _ f f' X Y r c g hf hf' hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hFd' : DifferentiableAt ℝ F' g :=
    (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
  have eX := h n ε E f F U g X hU hgU hg hF hfF hX
  refine ⟨?_, ?_, ?_⟩
  · rw [h n ε E f F U g (X + Y) hU hgU hg hF hfF (lie_algebra_add_mem ε hX hY), eX,
      h n ε E f F U g Y hU hgU hg hF hfF hY, Matrix.mul_add, map_add]
  · rw [h n ε E f F U g ((r : ℂ) • X) hU hgU hg hF hfF (lie_algebra_real_smul_mem ε hX r), eX,
      Matrix.mul_smul, Complex.coe_smul, map_smul, Complex.coe_smul]
  · have hsm : ContDiffOn ℝ ∞ (fun x => F x + c • F' x) (U ∩ U') :=
      (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
    rw [h n ε E (fun x => f x + c • f' x) (fun x => F x + c • F' x) (U ∩ U') g X (hU.inter hU')
      ⟨hgU, hgU'⟩ hg hsm (fun x hx hxJ => by rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]) hX,
      eX, h n ε E f' F' U' g X hU' hgU' hg hF' hfF' hX]
    have hD : HasFDerivAt (fun x => F x + c • F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
      hFd.hasFDerivAt.add (hFd'.hasFDerivAt.const_smul c)
    rw [hD.fderiv]
    simp

private lemma inG_commutator' {m : ℕ} {e : Fin m → Bool} {X Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : inG e X) (hY : inG e Y) : inG e (X * Y - Y * X) := by
  unfold inG at *
  have key : (X * Y - Y * X)ᴴ * Jm e + Jm e * (X * Y - Y * X) =
      Yᴴ * (Xᴴ * Jm e + Jm e * X) - (Yᴴ * Jm e + Jm e * Y) * X - Xᴴ * (Yᴴ * Jm e + Jm e * Y) +
        (Xᴴ * Jm e + Jm e * X) * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [key, hX, hY]
  simp

theorem rdBracketV_of (h : RdExtV) (_hs : RdSmoothV) : RdBracketV := by
  intro n ε E _ _ f X Y g hf hX hY hg
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hF1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hF).2
  let LX : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
  let LY : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ Y)
  have hGX : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y (y * X)) U :=
    hF1.clm_apply (LX.contDiff.contDiffOn)
  have hGY : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y (y * Y)) U :=
    hF1.clm_apply (LY.contDiff.contDiffOn)
  have eY : RdV X (RdV Y f) g = fderiv ℝ (fun y => fderiv ℝ F y (y * Y)) g (g * X) :=
    h n ε E (RdV Y f) (fun y => fderiv ℝ F y (y * Y)) U g X hU hgU hg hGY
      (fun x hx hxJ => h n ε E f F U x Y hU hx hxJ hF hfF hY) hX
  have eX : RdV Y (RdV X f) g = fderiv ℝ (fun y => fderiv ℝ F y (y * X)) g (g * Y) :=
    h n ε E (RdV X f) (fun y => fderiv ℝ F y (y * X)) U g Y hU hgU hg hGX
      (fun x hx hxJ => h n ε E f F U x X hU hx hxJ hF hfF hX) hY
  have eXY : RdV (X * Y - Y * X) f g = fderiv ℝ F g (g * (X * Y - Y * X)) :=
    h n ε E f F U g _ hU hgU hg hF hfF (inG_commutator' hX hY)
  have hFd2 : DifferentiableAt ℝ (fun y => fderiv ℝ F y) g :=
    (hF1.differentiableOn (by simp) g hgU).differentiableAt (hU.mem_nhds hgU)
  have hev : ∀ᶠ y in 𝓝 g, HasFDerivAt F (fderiv ℝ F y) y :=
    Filter.eventually_of_mem (hU.mem_nhds hgU) fun y hy =>
      ((hF.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hsymm := second_derivative_symmetric_of_eventually hev hFd2.hasFDerivAt (g * X) (g * Y)
  have hhY : HasFDerivAt (fun y => fderiv ℝ F y (y * Y)) _ g :=
    hFd2.hasFDerivAt.clm_apply LY.hasFDerivAt
  have hhX : HasFDerivAt (fun y => fderiv ℝ F y (y * X)) _ g :=
    hFd2.hasFDerivAt.clm_apply LX.hasFDerivAt
  have dY : fderiv ℝ (fun y => fderiv ℝ F y (y * Y)) g (g * X) =
      fderiv ℝ F g (g * X * Y) + fderiv ℝ (fun y => fderiv ℝ F y) g (g * X) (g * Y) := by
    rw [hhY.fderiv]
    rfl
  have dX : fderiv ℝ (fun y => fderiv ℝ F y (y * X)) g (g * Y) =
      fderiv ℝ F g (g * Y * X) + fderiv ℝ (fun y => fderiv ℝ F y) g (g * Y) (g * X) := by
    rw [hhX.fderiv]
    rfl
  have hsymm' : fderiv ℝ (fun y => fderiv ℝ F y) g (g * X) (g * Y) =
      fderiv ℝ (fun y => fderiv ℝ F y) g (g * Y) (g * X) := hsymm
  rw [eY, eX, eXY, dY, dX, hsymm', Matrix.mul_sub, map_sub, Matrix.mul_assoc g X Y,
    Matrix.mul_assoc g Y X]
  abel

section EabGl

variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma vector_right_derivative_neg (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hB : inG ε B) (hg : inUJ ε g) :
    RdV (-B) f g = -RdV B f g := by
  have h2 := (hl n ε E f f B B (-1) 0 g hf hf hB hB hg).2.1
  simpa using h2

lemma vector_right_derivative_add (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : RdV (A + B) f g = RdV A f g + RdV B f g := (hl n ε E f f A B 0 0 g hf hf hA hB hg).1

lemma vector_right_derivative_sub (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : RdV (A - B) f g = RdV A f g - RdV B f g := by
  have hnB : inG ε (-B) := by
    unfold inG at hB ⊢
    rw [Matrix.conjTranspose_neg, neg_mul, mul_neg, ← neg_add, hB, neg_zero]
  rw [sub_eq_add_neg A B, vector_right_derivative_add hl hf hA hnB hg, vector_right_derivative_neg hl hf hB hg, ← sub_eq_add_neg]

private lemma Jm_mul_JmRealPlaceTaylor {m : ℕ} (e : Fin m → Bool) : Jm e * Jm e = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private lemma Jm_mul_Jm_mulRealPlaceTaylor {m : ℕ} (e : Fin m → Bool) (Y : Matrix (Fin m) (Fin m) ℂ) :
    Jm e * (Jm e * Y) = Y := by
  rw [← Matrix.mul_assoc, Jm_mul_JmRealPlaceTaylor, Matrix.one_mul]

private lemma cpart1_inG {m : ℕ} (e : Fin m → Bool) (Z : Matrix (Fin m) (Fin m) ℂ) :
    inG e (cpart1 e Z) := by
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [star_div₀, star_one, star_ofNat]
  unfold inG cpart1
  rw [Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Jm_mul_JmRealPlaceTaylor, Jm_mul_Jm_mulRealPlaceTaylor, Matrix.mul_one, smul_sub]
  abel

private lemma cpart2_inG {m : ℕ} (e : Fin m → Bool) (Z : Matrix (Fin m) (Fin m) ℂ) :
    inG e (cpart2 e Z) := by
  have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', star_ofNat, Complex.star_def, Complex.conj_I]
    ring
  unfold inG cpart2
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Jm_mul_JmRealPlaceTaylor, Jm_mul_Jm_mulRealPlaceTaylor, Matrix.mul_one, smul_add]
  rw [hc]
  simp only [neg_smul]
  abel

lemma vector_complexified_derivative_sub (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnGV ε f) (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Z - W) f g = EcV ε Z f g - EcV ε W f g := by
  have h1 : cpart1 ε (Z - W) = cpart1 ε Z - cpart1 ε W := by
    simp only [cpart1, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  have h2 : cpart2 ε (Z - W) = cpart2 ε Z - cpart2 ε W := by
    simp only [cpart2, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, smul_add, smul_sub]
    abel
  simp only [EcV]
  rw [h1, h2, vector_right_derivative_sub hl hf (cpart1_inG ε Z) (cpart1_inG ε W) hg,
    vector_right_derivative_sub hl hf (cpart2_inG ε Z) (cpart2_inG ε W) hg, smul_sub]
  abel

lemma vector_complexified_derivative_zero (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : EcV ε 0 f g = 0 := by
  simp [EcV, RdV, cpart1, cpart2]

private lemma inG_sub_real_place_taylor {m : ℕ} {e : Fin m → Bool} {X Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : inG e X) (hY : inG e Y) : inG e (X - Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hX, hY, sub_zero]

private lemma Jm_mul_conjTranspose_mul_Jm_of_inG {m : ℕ} {e : Fin m → Bool} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : inG e A) : Jm e * Aᴴ * Jm e = -A := by
  unfold inG at hA
  have h : Jm e * Aᴴ * Jm e + A = Jm e * (Aᴴ * Jm e + Jm e * A) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_JmRealPlaceTaylor, Matrix.one_mul]
  rw [hA, Matrix.mul_zero] at h
  exact eq_neg_of_add_eq_zero_left h

private lemma cpart1_cpart2_add_I_smul_of_inG {m : ℕ} (e : Fin m → Bool) (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : inG e A) (hB : inG e B) :
    cpart1 e (A + Complex.I • B) = A ∧ cpart2 e (A + Complex.I • B) = B := by
  have hs : Jm e * (A + Complex.I • B)ᴴ * Jm e = -A + Complex.I • B := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Jm_mul_conjTranspose_mul_Jm_of_inG hA,
      Jm_mul_conjTranspose_mul_Jm_of_inG hB, neg_smul, smul_neg, neg_neg]
  have h2I : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  constructor
  · unfold cpart1
    rw [hs, show A + Complex.I • B - (-A + Complex.I • B) = (2 : ℂ) • A by rw [two_smul]; abel,
      smul_smul]
    norm_num
  · unfold cpart2
    rw [hs, show A + Complex.I • B + (-A + Complex.I • B) = (2 * Complex.I) • B by
        rw [mul_smul, two_smul]; abel,
      smul_smul, one_div, inv_mul_cancel₀ h2I, one_smul]

private lemma cpart1_add_I_smul_cpart2 {m : ℕ} (e : Fin m → Bool) (Z : Matrix (Fin m) (Fin m) ℂ) :
    cpart1 e Z + Complex.I • cpart2 e Z = Z := by
  unfold cpart1 cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add,
    show Z - Jm e * Zᴴ * Jm e + (Z + Jm e * Zᴴ * Jm e) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num

private lemma commutator_add_I_smul_expand {m : ℕ} (A1 A2 B1 B2 : Matrix (Fin m) (Fin m) ℂ) :
    (A1 + Complex.I • A2) * (B1 + Complex.I • B2) - (B1 + Complex.I • B2) * (A1 + Complex.I • A2) =
      ((A1 * B1 - B1 * A1) - (A2 * B2 - B2 * A2)) +
        Complex.I • ((A1 * B2 - B2 * A1) + (A2 * B1 - B1 * A2)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.I_mul_I, neg_one_smul, smul_add, smul_sub]
  abel

lemma vector_complexified_derivative_commutator (hl : RdLinV) (hb : RdBracketV) (hs : RdSmoothV)
    (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnGV ε f) (hg : inUJ ε g) :
    EcV ε Z (EcV ε W f) g - EcV ε W (EcV ε Z f) g = EcV ε (Z * W - W * Z) f g := by
  have hZ1 := cpart1_inG ε Z
  have hZ2 := cpart2_inG ε Z
  have hW1 := cpart1_inG ε W
  have hW2 := cpart2_inG ε W
  have L1 : ∀ X Y, inG ε X →
      RdV X (EcV ε Y f) g =
        RdV X (RdV (cpart1 ε Y) f) g + Complex.I • RdV X (RdV (cpart2 ε Y) f) g :=
    fun X Y hX =>
      (hl n ε E (RdV (cpart1 ε Y) f) (RdV (cpart2 ε Y) f) X X 0 Complex.I g
        (hs n ε E f _ hf (cpart1_inG ε Y)) (hs n ε E f _ hf (cpart2_inG ε Y)) hX hX hg).2.2
  have Bk : ∀ X Y, inG ε X → inG ε Y →
      RdV X (RdV Y f) g = RdV Y (RdV X f) g + RdV (X * Y - Y * X) f g := by
    intro X Y hX hY
    rw [← hb n ε E f X Y g hf hX hY hg]
    abel
  have hC := commutator_add_I_smul_expand (cpart1 ε Z) (cpart2 ε Z) (cpart1 ε W) (cpart2 ε W)
  rw [cpart1_add_I_smul_cpart2, cpart1_add_I_smul_cpart2] at hC
  have hP1 := inG_sub_real_place_taylor (inG_commutator' hZ1 hW1) (inG_commutator' hZ2 hW2)
  have hP2 := inG_add_real_place_taylor (inG_commutator' hZ1 hW2) (inG_commutator' hZ2 hW1)
  obtain ⟨hc1, hc2⟩ := cpart1_cpart2_add_I_smul_of_inG ε _ _ hP1 hP2
  simp only [EcV]
  rw [L1 _ W hZ1, L1 _ W hZ2, L1 _ Z hW1, L1 _ Z hW2,
    Bk _ _ hZ1 hW1, Bk _ _ hZ1 hW2, Bk _ _ hZ2 hW1, Bk _ _ hZ2 hW2, hC, hc1, hc2,
    vector_right_derivative_sub hl hf (inG_commutator' hZ1 hW1) (inG_commutator' hZ2 hW2) hg,
    vector_right_derivative_add hl hf (inG_commutator' hZ1 hW2) (inG_commutator' hZ2 hW1) hg]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

end EabGl

theorem eabGlV_of (hl : RdLinV) (hb : RdBracketV) (hs : RdSmoothV) : EabGlV := by
  intro n ε E _ _ f a b c d g hf hg
  unfold EabV
  rw [vector_complexified_derivative_commutator hl hb hs ε f _ _ g hf hg, vector_complexified_derivative_sub hl hf hg]
  have h1 : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne]
      exact h
  have h2 : Matrix.single c d (1 : ℂ) * Matrix.single a b 1 =
      if d = a then Matrix.single c b 1 else 0 := by
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne]
      exact h
  rw [h1, h2]
  split_ifs <;> simp [vector_complexified_derivative_zero]

theorem rdVPair_of (h : RdExtV) : RdVPair := by
  intro n ε E E' _ _ _ _ φ f X g hf hX hg
  have hsm : SmoothOnGV ε (fun x => φ (f x)) := by
    intro g0 hg0
    obtain ⟨U, F, hU, hg0U, hF, hfF⟩ := hf g0 hg0
    exact ⟨U, fun x => φ (F x), hU, hg0U, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF,
      fun x hx hxJ => by simp only [hfF x hx hxJ]⟩
  refine ⟨hsm, ?_⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp) g hgU).differentiableAt (hU.mem_nhds hgU)
  rw [h n ε E f F U g X hU hgU hg hF hfF hX,
    h n ε E' (fun x => φ (f x)) (fun x => φ (F x)) U g X hU hgU hg
      ((φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF)
      (fun x hx hxJ => by simp only [hfF x hx hxJ]) hX]
  have hcomp : fderiv ℝ (fun x => φ (F x)) g = (φ.restrictScalars ℝ).comp (fderiv ℝ F g) :=
    ((φ.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  rw [hcomp]
  rfl

end Formalism.REAL
