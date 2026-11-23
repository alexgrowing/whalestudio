import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponentStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
open Matrix

namespace GlobalTheory.RealLiftGen

theorem map_star_mul {l m n : Type} [Fintype m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, Matrix.map_apply, star_sum]

theorem map_star_star {m n : Type} (A : Matrix m n ℂ) : (A.map star).map star = A := by
  ext i j; simp

theorem Jm_map_star (R S : ℕ) : (Jm R S).map star = Jm R S := by
  rw [Jm, Formalism.UG.P.Jpq_eq_diagonal]; ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem Jm_mul_Jm (R S : ℕ) : Jm R S * Jm R S = 1 := Formalism.UG.P.Jpq_mul_self R S

theorem gen_of_cont {n : Type} [Fintype n] [DecidableEq n] (N : ℝ → Matrix n n ℂ) (hc : Continuous N)
    (h0 : N 0 = 1) (hm : ∀ s t, N (s + t) = N s * N t) : ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) :=
  GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous N hc h0 hm

theorem cont_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)} (γ : Multiplicative ℝ →* UG (cA σ) J)
    (hγ : Continuous γ) (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) :=
  GlobalTheory.T.continuous_unitaryOneParameter_realPlaceComponent γ hγ w τ

theorem piInf_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : AE F E) :
    piInf τ (cA σ x) = star (piInf τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a e =>
    have := h.1
    have h3 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) (evInf F w a)
    simp only [piInf, cA, compInf, RingHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.id_apply, infEmb_tmul]
    rw [star_mul', h.2.2.2 τ.1 e, ← h3, Complex.star_def, Complex.conj_ofReal]

theorem mem_upq_of {R S : ℕ} (Y : Mat R S)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᵀ * Jm R S * (NormedSpace.exp (t • Y)).map star = Jm R S) :
    Y ∈ upq R S := by
  have key : Yᵀ * Jm R S + Jm R S * Y.map star = 0 := by
    letI : NormedRing (Matrix (Ix R S) (Ix R S) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Ix R S) (Ix R S) ℂ) := Matrix.linftyOpNormedAlgebra
    have hs : ∀ A : Matrix (Ix R S) (Ix R S) ℂ, A.map star = Aᴴᵀ := fun A => by ext i j; rfl
    have e1 : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᵀ = NormedSpace.exp (t • Yᵀ) := fun t => by
      rw [← Matrix.exp_transpose, Matrix.transpose_smul]
    have e2 : ∀ t : ℝ, (NormedSpace.exp (t • Y)).map star = NormedSpace.exp (t • Y.map star) := fun t => by
      rw [hs, hs, ← Matrix.exp_conjTranspose, ← Matrix.exp_transpose, Matrix.conjTranspose_smul, Matrix.transpose_smul,
        star_trivial]
    have h1 := ((hasDerivAt_exp_smul_const (Yᵀ) (0:ℝ)).mul_const (Jm R S)).mul
      (hasDerivAt_exp_smul_const (Y.map star) (0:ℝ))
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h1
    have hc : ((fun y : ℝ => NormedSpace.exp (y • Yᵀ) * Jm R S) * fun u : ℝ => NormedSpace.exp (u • Y.map star)) =
        fun _ => Jm R S := funext fun t => by
      show NormedSpace.exp (t • Yᵀ) * Jm R S * NormedSpace.exp (t • Y.map star) = Jm R S
      rw [← e1, ← e2]; exact h t
    have h2 : HasDerivAt (fun _ : ℝ => Jm R S) (Yᵀ * Jm R S * 1 + Jm R S * Y.map star) 0 :=
      h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun hc t).symm)
    have h3 := h2.unique (hasDerivAt_const (0:ℝ) (Jm R S))
    simpa only [mul_one] using h3
  have h5 : (Yᵀ * Jm R S + Jm R S * Y.map star).map star = 0 := by rw [key]; ext; simp
  rw [Matrix.map_add _ (fun a b => star_add a b), map_star_mul, map_star_mul, map_star_star, Jm_map_star] at h5
  show Yᴴ * Jm R S + Jm R S * Y = 0
  exact h5

theorem genEx : GlobalTheory.RealLift.GenEx := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC γ hγ
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm R S := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm R S * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm R S), Matrix.mul_assoc (Jm R S), hF, Jm_mul_Jm]
    have h2 : (Jm R S * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm R S * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm R S * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : InfinitePlace F → ℝ → Matrix β β ℂ :=
    fun w t => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMm : ∀ w s t, M w (s + t) = M w s * M w t := by
    intro w s t
    simp only [hM, ofAdd_add, map_mul, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM0 : ∀ w, M w 0 = 1 := by
    intro w
    simp only [hM, ofAdd_zero, map_one, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ w t, (M w t)ᵀ * K w * (M w t).map star = K w := by
    intro w t
    have hg := (γ (Multiplicative.ofAdd t)).2
    change (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)))ᵀ * J *
      (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M w t)ᵀ * J.map (piInf (τ w)) * (M w t).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  set N : InfinitePlace F → ℝ → Mat R S := fun w t => A' w * M w t * C w with hN
  have hCN : ∀ w t, C w * N w t = M w t * C w := by
    intro w t; simp only [hN, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  have hNc : ∀ w, Continuous (N w) := fun w =>
    (continuous_const.matrix_mul (cont_map γ hγ.1 w (τ w))).matrix_mul continuous_const
  have hN0 : ∀ w, N w 0 = 1 := by intro w; simp only [hN, hM0, Matrix.mul_one, hAC]
  have hNm : ∀ w s t, N w (s + t) = N w s * N w t := by
    intro w s t
    simp only [hN, hMm]
    calc A' w * (M w s * M w t) * C w = A' w * M w s * (C w * A' w) * M w t * C w := by
          rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  choose Y hY using fun w => gen_of_cont (N w) (hNc w) (hN0 w) (hNm w)
  refine ⟨Y, fun w => mem_upq_of (Y w) fun t => ?_, fun t w => ?_⟩
  · rw [← hY w t, ← hF w]
    calc (N w t)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (N w t).map star
        = (C w * N w t)ᵀ * K w * (C w * N w t).map star := by
          simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = (C w)ᵀ * ((M w t)ᵀ * K w * (M w t).map star) * (C w).map star := by
          simp only [hCN, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = _ := by rw [hMu]
  · show M w t * C w = _
    rw [← hCN, hY]

end GlobalTheory.RealLiftGen
