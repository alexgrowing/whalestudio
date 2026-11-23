import CompanionTheory.ThickeningEstimates.LieGroupReduction.NormExpSubLe

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform

namespace CompanionTheory.ThKR.LL

variable {l : Type} [Fintype l] [DecidableEq l]

def bl (i j : l → l ⊕ l) : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] (Eu l →L[ℝ] Eu l) where
  toFun g := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (g.submatrix i j)
  map_add' g h := by rw [← map_add]; rfl
  map_smul' c g := by rw [RingHom.id_apply, ← map_smul]; rfl

theorem bl_apply (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (x : Eu l) (a : l) :
    bl i j g x a = ∑ b, g (i a) (j b) * x b := rfl

theorem pPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    pPart (g *ᵥ w) = bl Sum.inl Sum.inl g (pPart w) + bl Sum.inl Sum.inr g (qPart w) := by
  ext a
  simp [bl_apply, pPart, qPart, mulVec, dotProduct]

theorem qPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    qPart (g *ᵥ w) = bl Sum.inr Sum.inl g (pPart w) + bl Sum.inr Sum.inr g (qPart w) := by
  ext a
  simp [bl_apply, pPart, qPart, mulVec, dotProduct]

theorem det_bl (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) : (bl i j g).det = (g.submatrix i j).det :=
  LinearMap.det_toLin (EuclideanSpace.basisFun l ℝ).toBasis _

theorem block_inl_inl_one : bl Sum.inl Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]

theorem block_inl_inr_one : bl Sum.inl Sum.inr (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]

theorem block_inr_inl_one : bl Sum.inr Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]

theorem hasDerivAt_lin_exp {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] F)
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • X))) (L (NormedSpace.exp (t • X) * X)) t := by
  letI := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)

theorem exp_mul_exp_neg (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, add_neg_cancel, NormedSpace.exp_zero]

theorem sympl_exp {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (w w' : l ⊕ l → ℝ) :
    sympl (NormedSpace.exp X *ᵥ w) (NormedSpace.exp X *ᵥ w') = sympl w w' := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have hu : IsUnit (Matrix.J l ℝ) :=
    ⟨⟨Matrix.J l ℝ, -Matrix.J l ℝ, by rw [mul_neg, J_squared, neg_neg], by rw [neg_mul, J_squared, neg_neg]⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Xᵀ = Matrix.J l ℝ * -X * (Matrix.J l ℝ)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᵀ * (Matrix.J l ℝ * NormedSpace.exp X) = Matrix.J l ℝ := by
    have := exp_mul_exp_neg (-X)
    rw [neg_neg] at this
    rw [← Matrix.exp_transpose, h1, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.J l ℝ),
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_one]
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]

theorem intw_of_sympl {g : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hg : ∀ w w', sympl (g *ᵥ w) (g *ᵥ w') = sympl w w')
    (h : IsUnit (bl Sum.inl Sum.inl g)) (c : ℝ) (w : l ⊕ l → ℝ) :
    Intw (big (Ring.inverse (bl Sum.inl Sum.inl g)) (bl Sum.inl Sum.inr g) (bl Sum.inr Sum.inl g) c) (pPart w) (qPart w)
      (pPart (g *ᵥ w)) (qPart (g *ᵥ w)) := by
  have key : ∀ p q p' q' : Eu l, ⟪bl Sum.inl Sum.inl g p + bl Sum.inl Sum.inr g q,
      bl Sum.inr Sum.inl g p' + bl Sum.inr Sum.inr g q'⟫ - ⟪bl Sum.inr Sum.inl g p + bl Sum.inr Sum.inr g q,
      bl Sum.inl Sum.inl g p' + bl Sum.inl Sum.inr g q'⟫ = ⟪p, q'⟫ - ⟪q, p'⟫ := fun p q p' q' => by
    have := hg (Sum.elim (fun i => p i) fun i => q i) (Sum.elim (fun i => p' i) fun i => q' i)
    simp only [sympl, pPart_mulVec, qPart_mulVec] at this
    exact this
  rw [pPart_mulVec, qPart_mulVec]
  refine intw_big h.ringInverse (fun x => ?_) (fun x => ?_) (fun y z => ?_) (fun y z => ?_) (fun y z => ?_) c _ _
  · rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ h, ContinuousLinearMap.one_apply]
  · rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ h, ContinuousLinearMap.one_apply]
  · simpa [sub_eq_zero] using key y 0 z 0
  · simpa [sub_eq_zero] using key 0 y 0 z
  · simpa using key y 0 0 z

theorem fou_mq_fouInv (B : Matrix l l ℝ) (f : Sch l) :
    fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) B)) (fouInv l f)) =
      (4 * π * I : ℂ)⁻¹ • ∑ j, ∑ k, (B j k : ℂ) • (∂_{(EuclideanSpace.single j 1 : Eu l)}
        (∂_{(EuclideanSpace.single k 1 : Eu l)} f)) := by
  have e : ∀ u : Sch l, fou l (fouInv l u) = u := fun u => by
    rw [← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]
  rw [← e (_ • _)]
  congr 1
  have h : ∀ j (u : Sch l), fouInv l (dRho (Pi.single (Sum.inl j) 1) u) = -dRho (Pi.single (Sum.inr j) 1) (fouInv l u) :=
    fourierInv_dRho_inl
  simp only [← dRho_single_inl, map_smul, map_sum, h, map_neg, neg_neg]
  ext x
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [mq_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply, dRho_single_inr, smul_eq_mul,
    ContinuousLinearMap.neg_apply, inner_neg_right, inner_toEuclideanCLM, dotProduct, mulVec, Finset.mul_sum]
  push_cast
  simp only [mul_neg, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp
  ring

theorem quad_eq {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (f : Sch l) :
    quad X f = mq (bl Sum.inr Sum.inl X) f + vf (-bl Sum.inl Sum.inl X) f +
      fou l (mq (-bl Sum.inl Sum.inr X) (fouInv l f)) - ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f := by
  ext x
  have h := quad_fromBlocks (A := X.toBlocks₁₁) (B := X.toBlocks₁₂) (C := X.toBlocks₂₁) (D := X.toBlocks₂₂)
    (by rwa [fromBlocks_toBlocks]) f x
  rw [fromBlocks_toBlocks] at h
  have h2 := fou_mq_fouInv X.toBlocks₁₂ f
  have h3 : vf (-bl Sum.inl Sum.inl X) f x =
      -∑ j, ∑ k, (X.toBlocks₁₁ j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : Eu l)} f) x := by
    have : bl Sum.inl Sum.inl X x = ∑ j, ∑ k, (X.toBlocks₁₁ j k * x k) • (EuclideanSpace.single j 1 : Eu l) := by
      ext a
      simp [bl_apply, Pi.single_apply, toBlocks₁₁, Finset.sum_apply]
    rw [vf_apply, ContinuousLinearMap.neg_apply, this]
    simp [lineDerivOp_apply_eq_fderiv]
  have h4 : mq (bl Sum.inr Sum.inl X) f x = -(π * I * ∑ j, ∑ k, (X.toBlocks₂₁ j k : ℂ) * x j * x k * f x) := by
    have : ⟪x, bl Sum.inr Sum.inl X x⟫ = x ⬝ᵥ X.toBlocks₂₁ *ᵥ x := inner_toEuclideanCLM _ _ _
    rw [mq_apply, this]
    simp only [dotProduct, mulVec]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [SchwartzMap.sub_apply, SchwartzMap.add_apply]
  rw [h, h3, h4]
  erw [h2]
  simp only [SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul]
  push_cast
  ring

theorem differentiableAt_det {M : ℝ → Matrix l l ℝ} {t : ℝ} (h : ∀ i j, DifferentiableAt ℝ (fun t => M t i j) t) :
    DifferentiableAt ℝ (fun t => (M t).det) t := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun σ _ => (DifferentiableAt.fun_finset_prod fun i _ => h _ _).const_mul _

end CompanionTheory.ThKR.LL

namespace CompanionTheory.ThKR

open LL

theorem localLift_holds : LocalLift := by
  intro l _ _ X hX
  let g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => NormedSpace.exp (t • X)
  have g0 : g 0 = 1 := by simp [g]
  have hd := fun i j t => hasDerivAt_lin_exp (bl i j) X t
  let A : ℝ → Eu l →L[ℝ] Eu l := fun t => bl Sum.inl Sum.inl (g t)
  let c : ℝ → ℝ := fun t => (√|(A t).det|)⁻¹
  let V : ℝ → Sch l →L[ℂ] Sch l := fun t =>
    big (Ring.inverse (A t)) (bl Sum.inl Sum.inr (g t)) (bl Sum.inr Sum.inl (g t)) (c t)
  have A0 : A 0 = 1 := by simp only [A, g0, block_inl_inl_one]
  have hopen : ∀ t, IsUnit (A t) → ∀ᶠ u in 𝓝 t, IsUnit (A u) := fun t ht =>
    (hd _ _ t).continuousAt.eventually (Units.isOpen.mem_nhds ht)
  have hdet : ∀ t, IsUnit (A t) → (Ring.inverse (A t)).det * (A t).det = 1 := fun t ht => by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ ht)
    simpa [ContinuousLinearMap.det] using this
  have hne : ∀ t, IsUnit (A t) → (A t).det ≠ 0 := fun t ht => right_ne_zero_of_mul_eq_one (hdet t ht)
  have hc : ∀ t, IsUnit (A t) → c t ^ 2 = |(Ring.inverse (A t)).det| := fun t ht => by
    rw [eq_inv_of_mul_eq_one_left (hdet t ht), abs_inv, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc0 : ∀ t, IsUnit (A t) → c t ≠ 0 := fun t ht =>
    inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 (hne t ht))).ne'
  have hcd : ∀ t, IsUnit (A t) → DifferentiableAt ℝ c t := fun t ht => by
    have h1 : DifferentiableAt ℝ (fun t => (A t).det) t := by
      simp only [A, det_bl]
      exact differentiableAt_det fun i j =>
        (hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ (Sum.inl i) (Sum.inl j)) X t).differentiableAt
    exact ((h1.abs (hne t ht)).sqrt (abs_pos.2 (hne t ht)).ne').inv (Real.sqrt_pos.2 (abs_pos.2 (hne t ht))).ne'
  have c0 : c 0 = 1 := by simp [c, A0, ContinuousLinearMap.det]
  have V0 : V 0 = 1 := by simp only [V, A0, g0, c0, block_inl_inr_one, block_inr_inl_one, Ring.inverse_one, big_one]
  have hU : ∀ t, IsUnit (A t) → IsUnit (V t) := fun t ht => isUnit_big ht.ringInverse _ _ (hc0 t ht)
  have hI : ∀ t, IsUnit (A t) → Impl (fun w => g t *ᵥ w) (V t).toLinearMap := fun t ht =>
    ⟨iso_big ht.ringInverse _ _ (hc t ht), fun w => intw_of_sympl (sympl_exp (SMulMemClass.smul_mem t hX)) ht _ w⟩
  let v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ) := fun t w => NormedSpace.exp (t • -X) *ᵥ w
  have hv : ∀ t w a, HasDerivAt (fun t => v t w a) (((NormedSpace.exp (t • -X) * -X) *ᵥ w) a) t := fun t w a =>
    hasDerivAt_lin_exp ((LinearMap.proj a).comp ((Matrix.mulVecBilin ℝ ℝ).flip w)) (-X) t
  have hw : ∀ t, IsUnit (A t) → ∀ w f, dRho w (V t f) = V t (dRho (v t w) f) := fun t ht w f => by
    have hs : Function.Surjective (V t).toLinearMap := fun f => ⟨Ring.inverse (V t) f, by
      show (V t * Ring.inverse (V t)) f = f
      rw [Ring.mul_inverse_cancel _ (hU t ht), ContinuousLinearMap.one_apply]⟩
    have := Impl.dRho (s := Matrix.mulVecLin (g t)) (hI t ht) hs (v t w) f
    simp only [v, g, Matrix.mulVecLin_apply, mulVec_mulVec, smul_neg, exp_mul_exp_neg, one_mulVec] at this
    simp only [v, smul_neg]
    exact this.symm
  have hL := fun t (ht : IsUnit (A t)) (Ai' : Eu l →L[ℝ] Eu l) (h : HasDerivAt (fun t => Ring.inverse (A t)) Ai' t) =>
    ld_big h (hd Sum.inl Sum.inr t) (hd Sum.inr Sum.inl t) (hcd t ht).hasDerivAt
      ((hopen t ht).mono fun u hu => ⟨hu.ringInverse, hc u hu⟩)
  have h0 : IsUnit (A 0) := A0 ▸ isUnit_one
  obtain ⟨ε, hε, hA⟩ := Metric.eventually_nhds_iff.1 (hopen 0 h0)
  simp only [dist_zero_right, Real.norm_eq_abs] at hA
  refine ⟨ε, V, fun t => Ring.inverse (V t), (deriv c 0 : ℝ) + ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ), hε,
    fun f => by rw [V0]; rfl, fun t ht => ⟨fun f => ?_, fun f => ?_, hI t (hA ht)⟩, fun t ht f lam => ?_, fun f lam => ?_⟩
  · rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ (hU t (hA ht)), ContinuousLinearMap.one_apply]
  · rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ (hU t (hA ht)), ContinuousLinearMap.one_apply]
  · obtain ⟨Q, hQ, -⟩ := hL t (hA ht) _ ((hd Sum.inl Sum.inl t).differentiableAt.inverse (hA ht)).hasDerivAt
    exact hQ.differentiableAt v (fun w a => (hv t w a).differentiableAt) ((hopen t (hA ht)).mono hw) f lam
  · have h1 : HasDerivAt (fun t => Ring.inverse (A t)) (-bl Sum.inl Sum.inl X) 0 := by
      have h2 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Eu l →L[ℝ] Eu l)ˣ)).comp_hasDerivAt_of_eq 0
        (hd Sum.inl Sum.inl 0) A0.symm
      exact h2.congr_deriv (by
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one,
          one_mul, mul_one, zero_smul, NormedSpace.exp_zero])
    obtain ⟨Q, hQ, hQ'⟩ := hL 0 h0 _ h1
    have h3 := hQ' (by rw [A0, Ring.inverse_one]) (by rw [← block_inl_inr_one, ← g0]) (by rw [← block_inr_inl_one, ← g0]) c0
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    set z : ℂ := (deriv c 0 : ℝ) + ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) with hz
    have h4 : Q = ⇑(quad X + z • (1 : Sch l →L[ℂ] Sch l)) := by
      funext f
      rw [h3, ContinuousLinearMap.add_apply, quad_eq hX, hz, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        add_smul]
      abel
    rw [h4] at hQ
    refine hQ.hasDerivAt (fun f => ?_) v (fun w => X *ᵥ w) (fun w => by simp [v]) (fun w a => ?_) (fun w => ?_)
      ((hopen 0 h0).mono hw) f lam
    · exact congrArg (fun T : Sch l →L[ℂ] Sch l => T f) V0
    · simpa [neg_mulVec] using hv 0 w a
    · rw [← quad_comm hX, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      abel

end CompanionTheory.ThKR
