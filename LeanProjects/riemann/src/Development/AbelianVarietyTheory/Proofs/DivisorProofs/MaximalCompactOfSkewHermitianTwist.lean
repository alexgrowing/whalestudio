import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCpt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped Matrix TensorProduct

theorem exists_congr_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) : ∃ Q : GL (Fin n) ℂ, Q.1ᴴ * P * Q.1 = 1 := by
  have hd : P.det ≠ 0 := fun h => by
    obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [e] using hpos x hx
  obtain ⟨ε, Q, hQ⟩ := Frames.exists_congr_diagonal_sign hP hd
  refine ⟨Q, hQ.trans ?_⟩
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hx : Q.1 *ᵥ (Pi.single i 1 : Fin n → ℂ) ≠ 0 := fun h => by
    have := congrArg ((Q⁻¹).1 *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simpa using congrFun this i
  have := hpos _ hx
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ] at this
  cases h : ε i
  · simp [h, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.diagonal_apply] at this
    linarith
  · simp

theorem exists_unitary_sign {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (h2 : H * H = 1) :
    ∃ (ε : Fin n → Bool) (U : GL (Fin n) ℂ), U.1ᴴ * U.1 = 1 ∧
      U.1ᴴ * H * U.1 = Matrix.diagonal fun i => if ε i then 1 else -1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary.1 with hU
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
  have h1' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
  have h3 : Uᴴ * H * U = Matrix.diagonal fun i => (hH.eigenvalues i : ℂ) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have h4 : (Uᴴ * H * U) * (Uᴴ * H * U) = 1 := by
    calc _ = Uᴴ * (H * (U * Uᴴ) * H) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1', Matrix.mul_one, h2, Matrix.mul_one, h1]
  rw [h3, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at h4
  refine ⟨fun i => decide ((hH.eigenvalues i : ℂ) = 1), ⟨U, Uᴴ, h1', h1⟩, h1, h3.trans ?_⟩
  congr 1
  funext i
  have := congrFun (Matrix.diagonal_injective h4) i
  rcases mul_self_eq_one_iff.1 this with h | h
  · simp [h]
  · simp [h]

theorem exists_frame {n : ℕ} {M θ G : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (hθ : IsCartan M θ) {s : ℝ} (hs : s ≠ 0)
    (hG : G = (s : ℂ) • M.map star) : ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ),
      Q.1ᴴ * G * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → ((Q⁻¹).1 * k * Q.1)ᴴ * ((Q⁻¹).1 * k * Q.1) = 1 → Commute k θ := by
  obtain ⟨h1, h2, h3⟩ := hθ
  set N := M.map star with hN
  have hNh : Nᴴ = N := by
    ext i j
    simpa [hN] using congrArg star (congrFun (congrFun hM i) j)
  have h2' : θᴴ * N * θ = N := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    have e1 : θᵀ.map (starRingEnd ℂ) = θᴴ := by ext i j; simp
    have e2 : (θ.map star).map (starRingEnd ℂ) = θ := by ext i j; simp
    rw [e1, e2] at this
    exact this
  have h4 : θᴴ * N = N * θ := by
    conv_rhs => rw [← h2', Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨e, he, hes⟩ : ∃ e : ℝ, e * e = 1 ∧ 0 < s * e := by
    rcases lt_or_gt_of_ne hs with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by linarith⟩
  have he' : (e : ℂ) * e = 1 := by exact_mod_cast he
  set T := (e : ℂ) • θ with hT
  have hTT : T * T = 1 := by rw [hT, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he', one_smul, h1]
  have hGT : G * T = ((s * e : ℝ) : ℂ) • (θᴴ * N) := by
    rw [hG, hT, h4, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.ofReal_mul]
  have hGh : Gᴴ = G := by rw [hG, Matrix.conjTranspose_smul, hNh]; simp
  have hP : (G * T).IsHermitian := by
    rw [Matrix.IsHermitian, hGT, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hNh,
      Matrix.conjTranspose_conjTranspose, ← h4]
    simp
  obtain ⟨Q₀, hQ₀⟩ := exists_congr_one hP fun x hx => by
    have e1 : star x ⬝ᵥ (θᴴ * N) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp [dotProduct, Matrix.mulVec, hN, mul_comm]
    rw [hGT, Matrix.smul_mulVec, dotProduct_smul, e1, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_pos hes (by simpa using h3 x hx)
  have h5 : Q₀.1ᴴ * G = (Q₀⁻¹).1 * T := by
    have := congrArg (· * (Q₀⁻¹).1 * T) hQ₀
    simpa only [Matrix.mul_assoc, Units.mul_inv_cancel_left, hTT, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨ε, U, hU, hUH⟩ := exists_unitary_sign (H := Q₀.1ᴴ * G * Q₀.1)
    (Matrix.isHermitian_conjTranspose_mul_mul _ hGh) (by
      rw [h5]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
      rw [← Matrix.mul_assoc T, hTT, Matrix.one_mul, Units.inv_mul])
  refine ⟨ε, Q₀ * U, by simpa [Matrix.mul_assoc] using hUH, fun k hk hu => ?_⟩
  set Q := Q₀ * U with hQ
  have hQP : Q.1ᴴ * (G * T) * Q.1 = 1 := by
    calc _ = U.1ᴴ * (Q₀.1ᴴ * (G * T) * Q₀.1) * U.1 := by simp [hQ, Matrix.mul_assoc]
      _ = 1 := by rw [hQ₀, Matrix.mul_one, hU]
  have hi : (Q⁻¹).1ᴴ * Q.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hPe : G * T = (Q⁻¹).1ᴴ * (Q⁻¹).1 := by
    have := congrArg (fun A => (Q⁻¹).1ᴴ * A * (Q⁻¹).1) hQP
    simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right] using this
  have hkP : kᴴ * (G * T) * k = G * T := by
    have := congrArg (fun A => (Q⁻¹).1ᴴ * A * (Q⁻¹).1) hu
    rw [hPe]
    simpa only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one,
      Units.mul_inv_cancel_right] using this
  have hL : (Q.1 * Q.1ᴴ) * G * T = 1 := by
    rw [Matrix.mul_assoc, hPe, Matrix.mul_assoc, ← Matrix.mul_assoc Q.1ᴴ, ← Matrix.conjTranspose_mul, Units.inv_mul,
      Matrix.conjTranspose_one, Matrix.one_mul, Units.mul_inv]
  have hGu : IsUnit G := by
    have : IsUnit (Q.1 * Q.1ᴴ * G) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hL)
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hkG : IsUnit (kᴴ * G) := by
    rw [← hk, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hGu
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hGu)
  have hc : k * T = T * k := hkG.mul_left_cancel (by
    rw [← Matrix.mul_assoc, hk, ← hkP]; simp only [Matrix.mul_assoc])
  have := congrArg ((e : ℂ) • ·) hc
  simpa only [hT, Matrix.mul_smul, Matrix.smul_mul, smul_smul, he', one_smul, Commute, SemiconjBy] using this

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_evI_of_compFin {z : AE F E} (h : ∀ v, compFin F E v z = 0) : At (evI F) z := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun v => ?_
  · rw [Algebra.smul_def, map_mul, map_zero]
    refine mul_eq_zero_of_left ?_ _
    change evInf F w u ⊗ₜ[F] (1 : E) = 0
    rw [show evInf F w u = 0 from congrFun h1 w, TensorProduct.zero_tmul]
  · rw [Algebra.smul_def, map_mul, h, mul_zero, map_zero]

theorem exists_isMaxCpt_le_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∃ K, IsMaxCpt σ (c • W.J.map σ) K ∧ ∀ k ∈ K, (toGAd hσ W.J hc).symm k ∈ KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ hσ B d r s W hB hW c hc hσc
  have h := hB.cm
  have hcj : ∀ (τ : E →+* ℂ) x, star (τ x) = τ (σ x) := fun τ x => (h.2.2.2 τ x).symm
  have key : ∀ w : InfinitePlace F, ∃ (ε : Fin d → Bool) (Q : GL (Fin d) ℂ),
      Q.1ᴴ * (c • W.J.map σ).map (B.emb w).1 * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ k : Matrix (Fin d) (Fin d) ℂ, kᴴ * (c • W.J.map σ).map (B.emb w).1 * k = (c • W.J.map σ).map (B.emb w).1 →
        ((Q⁻¹).1 * k * Q.1)ᴴ * ((Q⁻¹).1 * k * Q.1) = 1 → Commute k (W.θ w) := fun w => by
    have hre : ((B.emb w).1 c).re = 0 := by
      have := congrArg Complex.re (hcj (B.emb w).1 c)
      rw [hσc, map_neg] at this
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have him : ((B.emb w).1 c).im ≠ 0 := fun e =>
      (map_ne_zero (B.emb w).1).2 hc (Complex.ext hre e)
    refine exists_frame (s := -((B.emb w).1 c).im) ?_ (hW.cartan w) (neg_ne_zero.2 him) ?_
    · ext i j
      simp [hcj, hW.skew]
    · ext i j
      have e : (B.emb w).1 c = ((B.emb w).1 c).im * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im ((B.emb w).1 c), hre]
        simp
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, star_mul', hcj]
      conv_lhs => rw [e]
      simp [mul_assoc]
  choose ε Q hQ hk using key
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective h (B.emb w))
  let b := fun w : InfinitePlace F => Formalism.UG.bc (e w).symm.toRingHom (Q w)
  have h1 : ∀ w, (b w).1.map (infEmb (B.emb w)) = (Q w).1 := fun w => Matrix.ext fun i j => (e w).apply_symm_apply _
  have h1' : ∀ w, ((b w)⁻¹).1.map (infEmb (B.emb w)) = ((Q w)⁻¹).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have h2 : ∀ w, (JR w.Completion (c • W.J.map σ)).map (infEmb (B.emb w)) = (c • W.J.map σ).map (B.emb w).1 := fun w => by
    ext r s; simp [JR, inclR]
  refine ⟨majCpt σ _ b, isMaxCpt_majCpt h fun w => ⟨ε w, Matrix.map_injective (e w).injective ?_⟩, fun k hkK => ?_⟩
  · change Matrix.map _ (infEmb (B.emb w)) = Matrix.map _ (infEmb (B.emb w))
    rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  obtain ⟨hk1, hk2⟩ := mem_majCpt.1 hkK
  have hm : mat ((toGAd hσ W.J hc).symm k) = (matHom _ σ _ k).1 := rfl
  refine ⟨fun u hu => Matrix.ext fun i j => at_evI_of_compFin (fun v => ?_) u hu, fun w => ?_⟩
  · have := congrArg (fun g => (matHom _ σ _ g).1 i j) (mem_infPts_iff_forall.1 hk1 v)
    rw [hm, Matrix.sub_apply, map_sub, sub_eq_zero]
    refine this.trans ?_
    simp [Matrix.one_apply, apply_ite (compFin F E v)]
  · have e1 : (mat ((toGAd hσ W.J hc).symm k)).map (piInf (B.emb w)) =
        (matHom _ σ _ (projArch σ _ w k)).1.map (infEmb (B.emb w)) := rfl
    rw [e1]
    refine hk w _ ?_ ?_
    · have : Formalism.UG.cT (sigR _ σ) (matHom _ σ _ (projArch σ _ w k)).1 * JR w.Completion (c • W.J.map σ) *
        (matHom _ σ _ (projArch σ _ w k)).1 = JR w.Completion (c • W.J.map σ) := (projArch σ _ w k).2
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2] using this
    · have : Formalism.UG.cT (sigR _ σ) ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 * 1 *
        ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 = 1 := mem_stabArch.1 (hk2 w)
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1',
        Matrix.map_one _ (map_zero _) (map_one _)] using this

end GlobalTheory.ThK.SqIntMaxCpt
