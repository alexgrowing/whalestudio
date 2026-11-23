import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasIwasawaArch
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame

noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped Matrix TensorProduct
open NumberField GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

theorem unitary_iff_commute {ι : Type} [Fintype ι] [DecidableEq ι] {Q Θ : Matrix ι ι ℂ} {s : ℂ} (hs : s ≠ 0) (hQ : IsUnit Q)
    (B g : GL ι ℂ) (hB : B.1ᴴ * (s • (Q * Θ)) * B.1 = 1) (hg : g.1ᴴ * Q * g.1 = Q) :
    (B⁻¹ * g * B).1ᴴ * (B⁻¹ * g * B).1 = 1 ↔ Commute g.1 Θ := by
  have u : ∀ x : GL ι ℂ, IsUnit x.1ᴴ := fun x => (Matrix.isUnit_conjTranspose _).2 x.isUnit
  have h1 : (B⁻¹).1ᴴ * (B⁻¹).1 = s • (Q * Θ) := by
    refine (u B).mul_left_cancel (B.isUnit.mul_right_cancel ?_)
    rw [hB, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, Units.inv_mul]; simp
  have h2 : (B⁻¹ * g * B).1ᴴ * (B⁻¹ * g * B).1 = B.1ᴴ * (s • (g.1ᴴ * Q * (Θ * g.1))) * B.1 := by
    simp only [Units.val_mul, Matrix.conjTranspose_mul]
    calc _ = B.1ᴴ * (g.1ᴴ * ((B⁻¹).1ᴴ * (B⁻¹).1) * g.1) * B.1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  rw [h2, ← hB, B.isUnit.mul_left_inj, (u B).mul_right_inj, (smul_right_injective _ hs).eq_iff]
  conv_lhs => rhs; rw [← hg, Matrix.mul_assoc]
  rw [((u g).mul hQ).mul_right_inj]
  exact eq_comm

theorem exists_cartan_frame {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hd : IsUnit M) (h : IsCartan M θ) {r : ℝ}
    (hr : r ≠ 0) : ∃ (b : GL (Fin n) ℂ) (ε : Fin n → Bool) (s : ℂ), s ≠ 0 ∧
      b.1ᴴ * ((r : ℂ) • Mᵀ) * b.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      b.1ᴴ * (s • (((r : ℂ) • Mᵀ) * θ)) * b.1 = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hM' : Mᵀᴴ = Mᵀ := congrArg Matrix.transpose hM
  have h4 : θᴴ * Mᵀ = Mᵀ * θ := by
    have e : θᴴ * Mᵀ * θ = Mᵀ := by
      conv_rhs => rw [← h2]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]; rfl
    calc _ = θᴴ * Mᵀ * (θ * θ) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e]
  set N : Matrix (Fin n) (Fin n) ℂ := ((|r| : ℝ) : ℂ) • (Mᵀ * θ) with hN
  have hr' : ((|r| : ℝ) : ℂ) ≠ 0 := by simpa using hr
  have hNh : N.IsHermitian := by
    change Nᴴ = N
    rw [hN, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hM', h4]; simp
  obtain ⟨ε, b, hb⟩ := Frames.exists_congr_diagonal_sign hNh (by
    rw [hN, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hr') (mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 hd).ne_zero
      (Matrix.isUnit_det_of_left_inverse h1).ne_zero))
  have hb1 : b.1ᴴ * N * b.1 = 1 := by
    rw [hb, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hx : (fun j => b.1 j i) ≠ 0 := fun e => by
      have := congrFun (congrFun b.inv_mul i) i
      simp [Matrix.mul_apply, show ∀ j, b.1 j i = 0 from congrFun e] at this
    have e : (b.1ᴴ * N * b.1) i i = ((|r| : ℝ) : ℂ) * ((θ *ᵥ fun j => b.1 j i) ⬝ᵥ M *ᵥ star fun j => b.1 j i) := by
      rw [hN, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, dotProduct_comm, ← Matrix.vecMul_transpose,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl
    have := mul_pos (abs_pos.2 hr) (h3 _ hx)
    rw [← Complex.re_ofReal_mul, ← e, hb, Matrix.diagonal_apply_eq] at this
    split_ifs at this ⊢
    · rfl
    · norm_num at this
  set s : ℂ := ((|r| : ℝ) : ℂ) / r with hs
  have hrc : (r : ℂ) ≠ 0 := by simpa using hr
  have hss : s * s = 1 := by
    rw [hs, div_mul_div_comm, ← Complex.ofReal_mul, abs_mul_abs_self, Complex.ofReal_mul, div_self (mul_ne_zero hrc hrc)]
  have hsN : s • (((r : ℂ) • Mᵀ) * θ) = N := by rw [Matrix.smul_mul, smul_smul, hs, div_mul_cancel₀ _ hrc]
  set S := b.1ᴴ * ((r : ℂ) • Mᵀ) * b.1 with hS
  have hSh : S.IsHermitian := by
    change Sᴴ = S
    simp [hS, Matrix.conjTranspose_smul, hM', Matrix.mul_assoc]
  have hS1 : S = s • ((b⁻¹).1 * θ * b.1) := by
    have : (r : ℂ) • Mᵀ = s • (N * θ) := by
      rw [← hsN, Matrix.smul_mul, smul_smul, hss, one_smul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e : b.1ᴴ * N = (b⁻¹).1 := by
      rw [← Matrix.one_mul (b⁻¹).1, ← hb1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [hS, this, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, e]
  have hS2 : S * S = 1 := by
    rw [hS1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, one_smul]
    calc _ = (b⁻¹).1 * θ * (b.1 * (b⁻¹).1) * θ * b.1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc _ θ θ, h1, Matrix.mul_one, Units.inv_mul]
  have hD := hSh.conjStarAlgAut_star_eigenvectorUnitary
  have hD2 := congrArg (Unitary.conjStarAlgAut ℂ _ (star hSh.eigenvectorUnitary)) hS2
  rw [map_mul, hD, map_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hD2
  rw [Unitary.conjStarAlgAut_star_apply] at hD
  set U := hSh.eigenvectorUnitary
  refine ⟨b * Unitary.toUnits U, fun i => decide (hSh.eigenvalues i = 1), s, left_ne_zero_of_mul_eq_one hss, ?_, ?_⟩
  · refine Eq.trans ?_ (hD.trans ?_)
    · simp only [hS, Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]; rfl
    · congr 1
      funext i
      have : (hSh.eigenvalues i : ℂ) * hSh.eigenvalues i = 1 := congrFun (Matrix.diagonal_injective hD2) i
      rcases mul_self_eq_one_iff.1 this with e | e
      · rw [if_pos (by simpa using e)]; exact e
      · rw [if_neg (by simp only [decide_eq_true_eq]; intro e'; rw [e'] at e; norm_num at e)]; exact e
  · rw [hsN, Units.val_mul, Matrix.conjTranspose_mul]
    calc _ = (Unitary.toUnits U).1ᴴ * (b.1ᴴ * N * b.1) * (Unitary.toUnits U).1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb1, Matrix.mul_one]; exact U.2.1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem exists_arch (hc : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {J : Matrix (Fin n) (Fin n) E}
    {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hd : IsUnit M) (h : IsCartan M θ) {r : ℝ} (hr : r ≠ 0)
    (hJ : J.map τ.1 = (r : ℂ) • Mᵀ) : ∃ b : GL (Fin n) (w.Completion ⊗[F] E),
      HasIwasawa σ (dblGram finSumFinEquiv J) (KArch σ _ w b) ∧ ∀ g : GArch σ (dblGram finSumFinEquiv J) w,
        g ∈ KArch σ _ w b ↔ Commute ((matHom _ σ _ g).1.map (infEmb τ)) (blkMat finSumFinEquiv θ (-θ)) := by
  obtain ⟨b, ε, s, hs, h1, h2⟩ := exists_cartan_frame hM hd h hr
  let e := RingEquiv.ofBijective _ (infEmb_bijective hc τ)
  have e1 : bc (infEmb τ) (bc e.symm.toRingHom b) = b := Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
  have e2 : ∀ {m : ℕ} (X : Matrix (Fin m) (Fin m) E), (JR w.Completion X).map (infEmb τ) = X.map τ.1 := fun X => by
    ext r s; simp [JR, inclR]
  have inj : ∀ {m : ℕ} {X Y : Matrix (Fin m) (Fin m) (w.Completion ⊗[F] E)}, X = Y ↔ X.map (infEmb τ) = Y.map (infEmb τ) :=
    (Matrix.map_injective e.injective).eq_iff.symm
  refine ⟨bc e.symm.toRingHom b, hasIwasawa_arch hc rfl w _ ε (inj.2 ?_), fun g => ?_⟩
  · rw [locGram, Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR hc, e2, hJ, Matrix.diagonal_map (map_zero _)]
    refine (show _ = _ from ?_).trans (h1.trans ?_)
    · conv_rhs => rw [← e1]
      rfl
    · congr 1; funext i; split_ifs <;> simp
  · have hQ : (dblGram finSumFinEquiv J).map τ.1 = blkMat finSumFinEquiv ((r : ℂ) • Mᵀ) (-((r : ℂ) • Mᵀ)) := by
      rw [dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), hJ]
    have hu : IsUnit ((r : ℂ) • Mᵀ).det := by
      rw [Matrix.det_smul, Matrix.det_transpose]
      exact (mul_ne_zero (pow_ne_zero _ (by simpa using hr)) ((Matrix.isUnit_iff_isUnit_det _).1 hd).ne_zero).isUnit
    refine Iff.trans ?_ (unitary_iff_commute (Q := (dblGram finSumFinEquiv J).map τ.1) hs ?_ (blkGL finSumFinEquiv (b, b))
      (bc (infEmb τ) (matHom _ σ _ g)) ?_ ?_)
    · rw [mem_stabArch]
      change _ * 1 * _ = 1 ↔ _
      rw [inj, Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR hc, Matrix.map_one _ (map_zero _) (map_one _)]
      conv_rhs => rw [← e1, ← bc_blkGL, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · rw [hQ, Matrix.isUnit_iff_isUnit_det, det_blkMat, Matrix.det_neg]
      exact hu.mul ((isUnit_one.neg.pow _).mul hu)
    · rw [hQ, blkMat_mul, neg_mul_neg, val_blkGL, show (blkMat finSumFinEquiv b.1 b.1)ᴴ = blkMat finSumFinEquiv b.1ᴴ b.1ᴴ from
        cT_blkMat _ (starRingEnd ℂ) _ _, Matrix.mul_smul, Matrix.smul_mul, blkMat_mul, blkMat_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul] at h2
      rw [← blkMat_one finSumFinEquiv, ← h2]
      exact (congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm finSumFinEquiv.symm) (Matrix.fromBlocks_smul s _ 0 0 _)).trans
        (by rw [smul_zero]; rfl)
    · have := inj.1 (show cT _ (matHom _ σ _ g).1 * JR _ _ * (matHom _ σ _ g).1 = JR _ _ from g.2)
      rwa [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR hc, e2] at this

end GlobalTheory.ThK.Dbl.Hgt

end
