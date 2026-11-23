import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LevelPointCoordinates

section mats

variable {j : ℕ}

theorem zfull_sub (W : Matrix (Fin j) (Fin j) ℂ) (σ τ : ℂ) :
    zfull W σ = zfull W τ + (σ - τ) • Matrix.single (Fin.last j) (Fin.last j) (1 : ℂ) := by
  ext a b
  have ha := a.isLt; have hb := b.isLt
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, zfull_apply, Fin.ext_iff, Fin.val_last,
    smul_eq_mul]
  split_ifs <;> first | (exfalso; omega) | ring1

theorem zfull_mul_single_last (W : Matrix (Fin j) (Fin j) ℂ) (σ : ℂ) :
    zfull W σ * Matrix.single (Fin.last j) (Fin.last j) (1 : ℂ) = σ • Matrix.single (Fin.last j) (Fin.last j) (1 : ℂ) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last j)]
  · have ha := a.isLt; have hb := b.isLt
    simp only [Matrix.smul_apply, Matrix.single_apply, zfull_apply, Fin.ext_iff, Fin.val_last, smul_eq_mul]
    split_ifs <;> (try simp only [true_and, and_true] at *) <;> first | (exfalso; omega) | ring1
  · intro c _ hc
    rw [Matrix.single_apply, if_neg (fun h => hc h.1.symm), mul_zero]
  · simp

theorem single_last_mul_w :
    Matrix.single (Fin.last j) (Fin.last j) (1 : ℂ) * G.wMat (j + 1) =
      Matrix.single (Fin.last j) (Fin.last j).rev (1 : ℂ) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last j)]
  · simp only [Matrix.single_apply, G.wMat, Matrix.of_apply]
    by_cases ha : a = Fin.last j <;> by_cases hb : b = (Fin.last j).rev <;>
      simp [ha, hb, Fin.rev_eq_iff, eq_comm]
  · intro c _ hc; simp [Matrix.single_apply, Ne.symm hc]
  · simp

theorem zfull_mul_single_rev (W : Matrix (Fin j) (Fin j) ℂ) (σ : ℂ) :
    zfull W σ * Matrix.single (Fin.last j) (Fin.last j).rev (1 : ℂ) =
      σ • Matrix.single (Fin.last j) (Fin.last j).rev (1 : ℂ) := by
  rw [← single_last_mul_w, ← Matrix.mul_assoc, zfull_mul_single_last, Matrix.smul_mul]

end mats

section torus

variable {k r j : ℕ}

def M1 (k r j : ℕ) (hj : j + 1 ≤ r) : B.Mat k r :=
  D.castM (by omega : j + 1 + (r - (j + 1)) = r)
    (U.blk3 0 0 0 0 0 0 (G.wMat (j + 1) * Matrix.single (Fin.last j) (Fin.last j) 1) 0 0)

def M2 (k r j : ℕ) (hj : j + 1 ≤ r) : B.Mat k r :=
  D.castM (by omega : j + 1 + (r - (j + 1)) = r)
    (U.blk3 0 0 (Matrix.single (Fin.last j) (Fin.last j) 1 * G.wMat (j + 1)) 0 0 0 0 0 0)

theorem x0_sub_tau_formula (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} (hZ : Z.det ≠ 0) {τ τ' : ℂ} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) (γ : B.Mat k (r - (j + 1))) :
    x0 k r j hj Z τ' γ = x0 k r j hj Z τ γ + (τ' - τ) • M1 k r j hj +
      ((star τ')⁻¹ - (star τ)⁻¹) • M2 k r j hj := by
  rw [level_point_eq_block_three, level_point_eq_block_three, zfull_conjTranspose_inv hZ hτ', zfull_conjTranspose_inv hZ hτ,
    zfull_sub _ (star τ')⁻¹ (star τ)⁻¹, zfull_sub Z τ' τ]
  unfold M1 M2
  rw [← castM_smul', ← castM_smul', ← castM_add', ← castM_add', smul_block_three, smul_block_three, Ux4.block3_add, Ux4.block3_add]
  congr 1
  congr 1 <;> simp only [smul_zero, add_zero, zero_add, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul]

theorem x0_mul_torus_element (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} (hZ : Z.det ≠ 0) {τ : ℂ} (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) (s : ℂ) :
    x0 k r j hj Z τ γ * hM k r j hj (Fin.last j) (Fin.last j) s =
      (s * τ) • M1 k r j hj - (star s * (star τ)⁻¹) • M2 k r j hj := by
  rw [level_point_eq_block_three, hM_blk, ← castM_mul', Ux4.block3_mul, zfull_conjTranspose_inv hZ hτ]
  unfold M1 M2
  rw [← castM_smul', ← castM_smul', ← castM_sub']
  congr 1
  rw [smul_block_three, smul_block_three]
  refine Ux4.ext_eB fun p q => ?_
  rw [Matrix.sub_apply, Ux4.block3_apply, Ux4.block3_apply, Ux4.block3_apply]
  rcases p with ((a | a) | a) <;> rcases q with ((b | b) | b) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.zero_apply,
      Matrix.smul_apply, smul_zero, sub_zero, zero_sub]
  ·
    rw [Matrix.mul_smul, Matrix.mul_assoc, show G.wMat (j + 1) * Matrix.single (Fin.last j).rev (Fin.last j).rev (1 : ℂ) =
      Matrix.single (Fin.last j) (Fin.last j).rev 1 from by
        ext c d
        rw [Ux3.wMat_mul_apply]
        simp only [Matrix.single_apply, Fin.rev_rev, Fin.rev_inj], zfull_mul_single_rev, ← single_last_mul_w]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  ·
    rw [Matrix.mul_smul, Matrix.mul_assoc, zfull_mul_single_last, Matrix.mul_smul]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring

end torus

section deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r j : ℕ}

theorem hM_inLie (hj : j + 1 ≤ r) (s : ℂ) : Q.inLieLev k r 0 (hM k r j hj (Fin.last j) (Fin.last j) s) :=
  ⟨hM_lie hj _ _ s, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

theorem hasFDerivAt_x0_in_tau (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} (hZ : Z.det ≠ 0) {τ : ℂ} (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) (s : ℂ) :
    ∃ L : ℂ →L[ℝ] B.Mat k r, HasFDerivAt (fun τ' : ℂ => x0 k r j hj Z τ' γ) L τ ∧
      L (s * τ) = x0 k r j hj Z τ γ * hM k r j hj (Fin.last j) (Fin.last j) s := by
  have hc : HasFDerivAt (⇑Complex.conjCLE) (Complex.conjCLE : ℂ →L[ℝ] ℂ) τ := Complex.conjCLE.hasFDerivAt
  have hτc : Complex.conjCLE τ ≠ 0 := by simpa using hτ
  have hi0 : HasFDerivAt (fun y : ℂ => y⁻¹)
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((Complex.conjCLE τ) ^ 2)⁻¹)) (Complex.conjCLE τ) :=
    hasFDerivAt_inv hτc
  have hi := (hi0.restrictScalars ℝ).comp τ hc
  have h1 := ((hasFDerivAt_id (𝕜 := ℝ) τ).sub_const τ).smul_const (M1 k r j hj)
  have h2 := (hi.sub_const ((star τ)⁻¹)).smul_const (M2 k r j hj)
  have h3 := (h1.add h2).const_add (x0 k r j hj Z τ γ)
  refine ⟨_, h3.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [isOpen_ne.mem_nhds hτ] with τ' hτ'
    rw [x0_sub_tau_formula hj hZ hτ hτ' γ]
    simp [Complex.conjCLE_apply, Complex.star_def, add_assoc]
  · rw [x0_mul_torus_element hj hZ hτ γ s]
    change (s * τ) • M1 k r j hj + ((starRingEnd ℂ (s * τ)) * (-((starRingEnd ℂ τ) ^ 2)⁻¹)) • M2 k r j hj = _
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    rw [map_mul]
    simp only [Complex.star_def]
    have : (starRingEnd ℂ) τ ≠ 0 := by simpa using hτ
    field_simp

theorem rdV_torus (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (hj : j + 1 ≤ r) (Dm : Set (Q.Mx k r))
    (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (hS : Q.SmoothLev k r 0 Dm Ψ) (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1)))
    (hx : x0 k r j hj Z τ γ ∈ Dm) (s : ℂ) :
    RdV (hM k r j hj (Fin.last j) (Fin.last j) s) Ψ (x0 k r j hj Z τ γ) =
      fderiv ℝ (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ (s * τ) := by
  have hxG : x0 k r j hj Z τ γ ∈ Q.Glev k r 0 := SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ hγ)
  obtain ⟨U, F, hU, hxU, hF, hFU⟩ := hS _ ⟨hxG, hx⟩
  have hd : DifferentiableAt ℝ F (x0 k r j hj Z τ γ) :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  have hrd := (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hxU hxG (hM_inLie hj s) hd hFU).deriv
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_x0_in_tau hj hZ hτ γ s
  have hcomp : HasFDerivAt (fun τ' => F (x0 k r j hj Z τ' γ)) ((fderiv ℝ F (x0 k r j hj Z τ γ)).comp L) τ :=
    hd.hasFDerivAt.comp τ hL
  have hev : (fun τ' => Ψ (x0 k r j hj Z τ' γ)) =ᶠ[𝓝 τ] fun τ' => F (x0 k r j hj Z τ' γ) := by
    have hmem : ∀ᶠ τ' in 𝓝 τ, x0 k r j hj Z τ' γ ∈ U := hL.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
    filter_upwards [hmem, isOpen_ne.mem_nhds hτ] with τ' h1 h2
    exact hFU _ h1 (SingleEntryHermitianProducts.glev0 (x0_GV hj hZ h2 hγ))
  unfold RdV
  rw [hrd, (hcomp.congr_of_eventuallyEq hev).fderiv, ContinuousLinearMap.comp_apply, hLv]

end deriv

section scal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem lin_decomp (D : ℂ →L[ℝ] E) (w : ℂ) : D w = (w.re : ℂ) • D 1 + (w.im : ℂ) • D Complex.I := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp <;> norm_num
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]

theorem half_I : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
  rw [one_div, mul_inv, Complex.inv_I]; ring

theorem torus_id (D : ℂ →L[ℝ] E) (τ : ℂ) :
    D (1 / 2 * τ) + Complex.I • D (-Complex.I / 2 * τ) = τ • ((1 / 2 : ℂ) • (D 1 - Complex.I • D Complex.I)) := by
  rw [lin_decomp D (1 / 2 * τ), lin_decomp D (-Complex.I / 2 * τ)]
  match_scalars <;> apply Complex.ext <;> simp <;> ring

theorem starTorus_id (D : ℂ →L[ℝ] E) (τ : ℂ) :
    D (-1 / 2 * τ) + Complex.I • D (-Complex.I / 2 * τ) =
      -(conj τ • ((1 / 2 : ℂ) • (D 1 + Complex.I • D Complex.I))) := by
  rw [lin_decomp D (-1 / 2 * τ), lin_decomp D (-Complex.I / 2 * τ)]
  match_scalars <;> apply Complex.ext <;> simp <;> ring

end scal

section final

variable {k r j : ℕ}

theorem hpart1_EE (hj : j + 1 ≤ r) :
    hpart1 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) (Fin.last j) (1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI, smul_sub]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]
  rfl

theorem hpart2_EE (hj : j + 1 ≤ r) :
    hpart2 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) (Fin.last j) (-Complex.I / 2) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_add, half_I]
  have h2 : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [h2, neg_smul, sub_neg_eq_add]
  rfl

theorem hpart1_SS (hj : j + 1 ≤ r) :
    hpart1 (Hpk k r) (Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) (Fin.last j) (-1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_esI, single_mul_hpk_esI]
  have h2 : star (-1 / 2 : ℂ) = -1 / 2 := by
    apply Complex.ext <;> norm_num
  rw [h2]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Fin.val_last]
  ring

theorem hpart2_SS (hj : j + 1 ≤ r) :
    hpart2 (Hpk k r) (Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) (Fin.last j) (-Complex.I / 2) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_esI, single_mul_hpk_esI, half_I]
  have h2 : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by
    apply Complex.ext <;> simp <;> norm_num
  rw [h2]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul, Fin.val_last]
  ring

theorem torus_action_x0 : TorusDirectionAtBasePoint := by
  intro E _ _ k r j hj Dm Ψ Z τ γ hD hS hZ hτ hγ hx
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_EE hj, hpart2_EE hj, rdV_torus E hj Dm Ψ Z τ γ hS hZ hτ hγ hx,
    rdV_torus E hj Dm Ψ Z τ γ hS hZ hτ hγ hx]
  unfold PBP.dz
  exact torus_id _ τ

theorem star_torus_x0 : ConjugateTorusDirectionAtBasePoint := by
  intro E _ _ k r j hj Dm Ψ Z τ γ hD hS hZ hτ hγ hx
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_SS hj, hpart2_SS hj, rdV_torus E hj Dm Ψ Z τ γ hS hZ hτ hγ hx,
    rdV_torus E hj Dm Ψ Z τ γ hS hZ hτ hγ hx]
  unfold PBP.dzb
  exact starTorus_id _ τ

end final

end Formalism.FourierDecayAlt.P.CutHL
