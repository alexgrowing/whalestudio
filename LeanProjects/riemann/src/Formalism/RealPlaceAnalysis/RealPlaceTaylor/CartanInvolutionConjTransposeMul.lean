import Formalism.RealPlaceAnalysis.SmoothOnG
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

section F3ALinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

lemma hasDerivAt_matrix_exp_smul_at_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end F3ALinfty

lemma tendsto_slope_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_matrix_exp_smul_at_zero X).tendsto_slope

lemma tendsto_slope_mul_exp_smul {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by
  have h := (tendsto_slope_exp_smul X).const_mul g
  refine h.congr (fun t => ?_)
  simp only [slope_def_module, Matrix.mul_sub, Matrix.mul_smul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma hasDerivAt_mul_exp_smul_zero {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  hasDerivAt_iff_tendsto_slope.mpr (tendsto_slope_mul_exp_smul g X)

lemma indefinite_unitary_mul_mem {n : ℕ} (ε : Fin n → Bool) {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : inUJ ε a) (hb : inUJ ε b) : inUJ ε (a * b) := by
  unfold inUJ at *
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

lemma lie_algebra_add_mem {n : ℕ} (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

lemma lie_algebra_real_smul_mem {n : ℕ} (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (r : ℝ) : inG ε ((r : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem right_derivative_extends : RdExt := by
  intro n ε f F U g X hU hg hgJ hF hfF hX
  unfold Rd
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

theorem right_derivative_left_invariant : RdLeft := by
  intro n f X h g
  simp only [Rd, Matrix.mul_assoc]

theorem rdLin_of (h : RdExt) : RdLin := by
  intro n ε f f' X Y r c g hf hf' hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hFd' : DifferentiableAt ℝ F' g :=
    (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
  have eX := h n ε f F U g X hU hgU hg hF hfF hX
  refine ⟨?_, ?_, ?_⟩
  · rw [h n ε f F U g (X + Y) hU hgU hg hF hfF (lie_algebra_add_mem ε hX hY), eX,
      h n ε f F U g Y hU hgU hg hF hfF hY, Matrix.mul_add, map_add]
  · rw [h n ε f F U g ((r : ℂ) • X) hU hgU hg hF hfF (lie_algebra_real_smul_mem ε hX r), eX,
      Matrix.mul_smul, Complex.coe_smul, map_smul, Complex.real_smul]
  · have hsm : ContDiffOn ℝ ∞ (fun x => F x + c * F' x) (U ∩ U') :=
      (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right))
    rw [h n ε (fun x => f x + c * f' x) (fun x => F x + c * F' x) (U ∩ U') g X (hU.inter hU')
      ⟨hgU, hgU'⟩ hg hsm (fun x hx hxJ => by rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]) hX,
      eX, h n ε f' F' U' g X hU' hgU' hg hF' hfF' hX]
    have hD : HasFDerivAt (fun x => F x + c * F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
      hFd.hasFDerivAt.add (hFd'.hasFDerivAt.const_mul c)
    rw [hD.fderiv]
    simp

theorem right_derivative_linear : RdLin := rdLin_of right_derivative_extends

lemma signature_mul_signature_mul {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

lemma cartan_involution_conjTranspose_mul {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Jm ε * Zᴴ * Jm ε)ᴴ * Jm ε = Jm ε * Z := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self,
    Matrix.mul_one]

lemma signature_mul_cartan_involution {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
  rw [Matrix.mul_assoc, signature_mul_signature_mul]

lemma star_one_half : star (1 / 2 : ℂ) = 1 / 2 := by simp

lemma star_one_div_two_I : star (1 / (2 * Complex.I) : ℂ) = - (1 / (2 * Complex.I)) := by
  simp [Complex.conj_I]

theorem complex_parts_mem_lie_algebra_holds : CpartMem := by
  intro n ε Z
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inG cpart1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_sub, signature_mul_cartan_involution, star_one_half, ← smul_add]
    simp
  · unfold inG cpart2
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_add, signature_mul_cartan_involution, star_one_div_two_I, neg_smul,
      add_comm (Jm ε * Z), neg_add_cancel]
  · unfold cpart1 cpart2
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    unfold inG at hX
    have hA : Jm ε * Zᴴ * Jm ε = -Z := by
      rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hX, Matrix.mul_neg, signature_mul_signature_mul]
    unfold cpart1 cpart2
    rw [hA, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num

end Formalism.REAL
