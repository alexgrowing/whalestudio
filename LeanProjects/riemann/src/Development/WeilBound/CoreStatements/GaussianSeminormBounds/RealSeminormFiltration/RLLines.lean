import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace PositivityTheory.RL

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_oneParam (A : ℝ → 𝔸) (hc : Continuous A) (h0 : A 0 = 1)
    (hm : ∀ s t, A (s + t) = A s * A t) : ∃ Y : 𝔸, HasDerivAt A Y 0 := by
  let C : ℝ → 𝔸 := fun x => ∫ s in (0 : ℝ)..x, A s
  have hC : ∀ x, HasDerivAt C (A x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hC0 : C 0 = 0 := by simp [C]
  obtain ⟨ε, hε, hu⟩ : ∃ ε : ℝ, ε ≠ 0 ∧ IsUnit (C ε) := by
    have hs := hasDerivAt_iff_tendsto_slope.1 (hC 0)
    rw [h0] at hs
    have hU : ∀ᶠ x in nhdsWithin (0 : ℝ) {0}ᶜ, IsUnit (slope C 0 x) :=
      hs.eventually (Units.isOpen.mem_nhds isUnit_one)
    have hne : ∀ᶠ x in nhdsWithin (0 : ℝ) {0}ᶜ, x ≠ 0 := eventually_mem_nhdsWithin
    obtain ⟨x, hx, hx0⟩ := (hU.and hne).exists
    refine ⟨x, hx0, ?_⟩
    have e : C x = x • slope C 0 x := by
      simp only [slope, hC0, sub_zero, vsub_eq_sub, smul_smul]
      rw [mul_inv_cancel₀ hx0, one_smul]
    rw [e]
    have hxu : IsUnit (algebraMap ℝ 𝔸 x) := (IsUnit.mk0 x hx0).map (algebraMap ℝ 𝔸)
    rw [Algebra.smul_def]
    exact hxu.mul hx
  obtain ⟨u, hu⟩ := hu
  have key : ∀ t, A t * C ε = C (t + ε) - C t := fun t => by
    have e1 : A t * C ε = ∫ s in (0 : ℝ)..ε, A t * A s :=
      ((ContinuousLinearMap.mul ℝ 𝔸 (A t)).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)).symm
    have e2 : (∫ s in (0 : ℝ)..ε, A t * A s) = ∫ s in t..(t + ε), A s := by
      have := intervalIntegral.integral_comp_add_left (a := 0) (b := ε) A t
      simp only [add_zero] at this
      rw [← this]
      exact intervalIntegral.integral_congr fun s _ => (hm t s).symm
    rw [e1, e2]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have hA : A = fun t => (C (t + ε) - C t) * (↑u⁻¹ : 𝔸) := by
    funext t
    rw [← key, ← hu, mul_assoc, Units.mul_inv, mul_one]
  have hd : HasDerivAt (fun t => C (t + ε) - C t) (A (0 + ε) - A 0) 0 :=
    ((hC (0 + ε)).comp_add_const 0 ε).sub (hC 0)
  exact ⟨_, (hd.mul_const (↑u⁻¹ : 𝔸)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => congrFun hA t)⟩

theorem eq_exp_of_hasDerivAt (A : ℝ → 𝔸) (h0 : A 0 = 1) (hm : ∀ s t, A (s + t) = A s * A t) {Y : 𝔸}
    (hY : HasDerivAt A Y 0) (t : ℝ) : A t = NormedSpace.exp (t • Y) := by
  let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hd : ∀ s, HasDerivAt A (A s * Y) s := fun s => by
    have h1 : HasDerivAt (fun x => A (x - s)) Y s := by
      have : HasDerivAt A Y (s - s) := by rw [sub_self]; exact hY
      exact this.comp_sub_const s s
    refine (h1.const_mul (A s)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show A x = A s * A (x - s)
    rw [← hm, add_sub_cancel]
  have hf : ∀ s, HasDerivAt (fun x : ℝ => A x * NormedSpace.exp (x • (-Y))) 0 s := fun s => by
    have := (hd s).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) s)
    exact this.congr_deriv (by simp [mul_assoc])
  have hk := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt) (fun s => (hf s).deriv) t 0
  simp only [zero_smul, NormedSpace.exp_zero, h0, mul_one] at hk
  have hc : Commute (t • (-Y)) (t • Y) := ((Commute.refl Y).neg_left.smul_left t).smul_right t
  calc A t = A t * NormedSpace.exp (t • (-Y) + t • Y) := by simp
    _ = NormedSpace.exp (t • Y) := by rw [NormedSpace.exp_add_of_commute hc, ← mul_assoc, hk, one_mul]

theorem exists_gen [StarRing 𝔸] [ContinuousStar 𝔸] [StarModule ℝ 𝔸] (A : ℝ → 𝔸) (hc : Continuous A) (h0 : A 0 = 1)
    (hm : ∀ s t, A (s + t) = A s * A t) (J : 𝔸) (hJ : ∀ t, star (A t) * J * A t = J) :
    ∃ Y : 𝔸, star Y * J + J * Y = 0 ∧ ∀ t : ℝ, A t = NormedSpace.exp (t • Y) := by
  obtain ⟨Y, hY⟩ := hasDerivAt_oneParam A hc h0 hm
  refine ⟨Y, ?_, eq_exp_of_hasDerivAt A h0 hm hY⟩
  have h1 := (hY.star.mul_const J).mul hY
  have h2 : HasDerivAt (fun t => star (A t) * J * A t) 0 0 := by
    simp only [hJ]
    exact hasDerivAt_const _ _
  have h3 := h1.unique h2
  simpa [h0] using h3

end Banach

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exists_gen_matrix (A : ℝ → Matrix ι ι ℂ) (hc : Continuous A) (h0 : A 0 = 1)
    (hm : ∀ s t, A (s + t) = A s * A t) (J : Matrix ι ι ℂ) (hJ : ∀ t, (A t)ᴴ * J * A t = J) :
    ∃ Y : Matrix ι ι ℂ, Yᴴ * J + J * Y = 0 ∧ ∀ t : ℝ, A t = NormedSpace.exp (t • Y) := by
  have : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℝ _
  have : @ContinuousStar (Matrix ι ι ℂ) PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
    ⟨continuous_id.matrix_conjTranspose⟩
  exact exists_gen A hc h0 hm J hJ

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem continuous_exp_smul (Y : Matrix ι ι ℂ) : Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
  have : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℝ _
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y t).continuousAt

theorem exp_add_smul (Y : Matrix ι ι ℂ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem semiconjBy_exp {J X Y : Matrix ι ι ℂ} (h : SemiconjBy J X Y) : J * NormedSpace.exp X = NormedSpace.exp Y * J :=
  SemiconjBy.exp_right (𝔸 := Matrix ι ι ℂ) h

theorem exp_preserves {Y J : Matrix ι ι ℂ} (h : Yᴴ * J + J * Y = 0) :
    (NormedSpace.exp Y)ᴴ * J * NormedSpace.exp Y = J := by
  have hs : SemiconjBy J (-Y) Yᴴ := by
    show J * -Y = Yᴴ * J
    rw [Matrix.mul_neg, eq_neg_of_add_eq_zero_left h]
  have he : J * NormedSpace.exp (-Y) = NormedSpace.exp Yᴴ * J := semiconjBy_exp hs
  rw [← Matrix.exp_conjTranspose, ← he, Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left]
  simp

open scoped Matrix.Norms.L2Operator in

theorem exists_log_unitary {k J : Matrix ι ι ℂ} (hk : kᴴ * k = 1) (hJ : Jᴴ = J) (hc : Commute k J) :
    ∃ Y : Matrix ι ι ℂ, Yᴴ = -Y ∧ Commute Y J ∧ NormedSpace.exp Y = k := by
  have hku : k ∈ unitary (Matrix ι ι ℂ) := Matrix.mem_unitaryGroup_iff'.2 hk
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, -Complex.exp (θ * Complex.I) ∉ spectrum ℂ k := by
    by_contra hall
    push Not at hall
    have hinj : Set.InjOn (fun θ : ℝ => -Complex.exp (θ * Complex.I)) (Set.Ioo 0 1) := by
      intro x hx y hy hxy
      have h1 := congrArg Complex.re (neg_injective hxy)
      rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at h1
      have := Real.pi_gt_three
      exact Real.injOn_cos ⟨hx.1.le, by linarith [hx.2]⟩ ⟨hy.1.le, by linarith [hy.2]⟩ h1
    exact Set.Ioo_infinite (zero_lt_one' ℝ)
      (Set.Finite.of_injOn (fun θ _ => hall θ) hinj (Matrix.finite_spectrum k))
  set z : ℂ := Complex.exp (θ * Complex.I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hz1 : star z * z = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hz, Complex.norm_exp_ofReal_mul_I]; simp
  have hzi : star z⁻¹ * z⁻¹ = 1 := by rw [star_inv₀, ← mul_inv, hz1, inv_one]
  have huu : z⁻¹ • k ∈ unitary (Matrix ι ι ℂ) := by
    refine Matrix.mem_unitaryGroup_iff'.2 ?_
    rw [star_smul, smul_mul_smul_comm, hzi, one_smul]
    exact hk
  let u : unitary (Matrix ι ι ℂ) := ⟨z⁻¹ • k, huu⟩
  have hsp : (-1 : ℂ) ∉ spectrum ℂ (u : Matrix ι ι ℂ) := fun h => hθ (by
    have := (spectrum.smul_mem_smul_iff (a := (u : Matrix ι ι ℂ)) (s := (-1 : ℂ)) (r := Units.mk0 z hz0)).2 h
    simpa [u, Units.smul_def, smul_smul, mul_inv_cancel₀ hz0] using this)
  have hn : ‖(u : Matrix ι ι ℂ) - 1‖ < 2 := (Unitary.norm_sub_one_lt_two_iff huu).2 hsp
  have he := congrArg Subtype.val (expUnitary_argSelfAdjoint hn)
  set X := Unitary.argSelfAdjoint u with hX
  have hXs : (X : Matrix ι ι ℂ)ᴴ = X := X.2
  have hc1 : Commute (u : Matrix ι ι ℂ) J := hc.smul_left _
  have hc2 : Commute (star (u : Matrix ι ι ℂ)) J := by
    have := hc1.star_star
    rwa [Matrix.star_eq_conjTranspose J, hJ] at this
  have hXc : Commute (X : Matrix ι ι ℂ) J := hc1.cfc hc2 _
  refine ⟨Complex.I • (X : Matrix ι ι ℂ) + (θ * Complex.I : ℂ) • 1, ?_, ?_, ?_⟩
  · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hXs, add_comm]
  · exact (hXc.smul_left _).add_left ((Commute.one_left J).smul_left _)
  · rw [Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _)]
    have e1 : NormedSpace.exp (Complex.I • (X : Matrix ι ι ℂ)) = z⁻¹ • k := he
    have e2 : NormedSpace.exp ((θ * Complex.I : ℂ) • (1 : Matrix ι ι ℂ)) = z • 1 := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      rw [Pi.coe_exp, hz, Complex.exp_eq_exp_ℂ]
    rw [e1, e2, smul_mul_smul_comm, inv_mul_cancel₀ hz0, one_smul, mul_one]

end Mat

section Frame

variable {R S : ℕ} {β : Type} [Fintype β] [DecidableEq β]

theorem Jm_eq : Jm R S = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) fun _ => -1) := by
  have h : Jm R S = Matrix.fromBlocks 1 0 0 (-1) := rfl
  rw [h, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, ← Matrix.diagonal_neg, Matrix.diagonal_one]

theorem Jm_mul_self : Jm R S * Jm R S = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases a with a | a <;> simp

theorem Jm_map_star : (Jm R S).map star = Jm R S := by
  rw [Jm_eq, Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  rcases a with a | a <;> simp

theorem Jm_conjTranspose : (Jm R S)ᴴ = Jm R S := by
  rw [Matrix.conjTranspose, Jm_eq, Matrix.diagonal_transpose, ← Jm_eq, Jm_map_star]

theorem isKC_of_commute {Y : Mat R S} (h : Commute Y (Jm R S)) : IsKC Y := by
  intro a b hab
  have e := congrFun (congrFun h.eq a) b
  rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  rcases a with a | a <;> rcases b with b | b
  · exact absurd trivial hab
  · simp only [Sum.elim_inl, Sum.elim_inr] at e
    linear_combination (-1 / 2) * e
  · simp only [Sum.elim_inl, Sum.elim_inr] at e
    linear_combination (1 / 2) * e
  · exact absurd trivial hab

theorem map_star_mul {l m n : Type} [Fintype m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    (A * B).map star = A.map star * B.map star := Matrix.map_mul (f := starRingEnd ℂ)

theorem map_star_one {n : Type} [DecidableEq n] : (1 : Matrix n n ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem frame_inv {M : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} (h : IsFrame M C) :
    ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1 ∧ C' * C = 1 := by
  obtain ⟨h1, C', h2⟩ := h
  refine ⟨C', h2, ?_⟩
  have h3 : (M * C.map star * Jm R S)ᵀ * C = 1 := by
    have : Cᵀ * (M * C.map star * Jm R S) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Jm_mul_self]
    rw [← Matrix.transpose_one, ← this, Matrix.transpose_mul Cᵀ, Matrix.transpose_transpose]
  have h4 : C' = (M * C.map star * Jm R S)ᵀ := by
    rw [← Matrix.one_mul C', ← h3, Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [h4, h3]

theorem conj_form (h : Mat R S) : (hᴴ * Jm R S * h).map star = hᵀ * Jm R S * h.map star := by
  rw [map_star_mul, map_star_mul, Jm_map_star]
  congr 2
  ext i j
  simp

theorem frame_iff {M : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} (hC : IsFrame M C) {g : Matrix β β ℂ} {h : Mat R S}
    (hg : g * C = C * h) : gᵀ * M * g.map star = M ↔ hᴴ * Jm R S * h = Jm R S := by
  obtain ⟨C', h1, -⟩ := frame_inv hC
  have key : Cᵀ * (gᵀ * M * g.map star) * C.map star = (hᴴ * Jm R S * h).map star := by
    rw [conj_form, ← hC.1]
    calc Cᵀ * (gᵀ * M * g.map star) * C.map star = (g * C)ᵀ * M * (g * C).map star := by
          simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [hg]
          simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
  constructor
  · intro e
    rw [e, hC.1] at key
    exact Matrix.map_injective star_injective (key.symm.trans Jm_map_star.symm)
  · intro e
    rw [e, Jm_map_star, ← hC.1] at key
    have can : ∀ X : Matrix β β ℂ, C'ᵀ * (Cᵀ * X * C.map star) * C'.map star = X := fun X => by
      calc _ = (C * C')ᵀ * X * (C * C').map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = X := by rw [h1, Matrix.transpose_one, map_star_one, Matrix.one_mul, Matrix.mul_one]
    rw [← can (gᵀ * M * g.map star), key, can]

theorem frame_iff_smul {b : ℂ} {M : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} (hC : IsFrame (b • M) C) {g : Matrix β β ℂ}
    {h : Mat R S} (hg : g * C = C * h) : gᵀ * M * g.map star = M ↔ hᴴ * Jm R S * h = Jm R S := by
  rw [← frame_iff hC hg, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun e => by rw [e], fun e => ?_⟩
  by_cases hb : b = 0
  · obtain ⟨h1, C', h2⟩ := hC
    have h3 : (1 : Mat R S) = 0 := by
      rw [← Jm_mul_self, ← h1, hb]
      simp
    have h4 : (1 : Matrix β β ℂ) = 0 := by
      rw [← h2, ← Matrix.mul_one C, h3]
      simp
    rw [← Matrix.mul_one M, h4]
    simp
  · exact smul_right_injective _ hb e

end Frame

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ β : E, σ β ≠ β := by
  by_contra hne
  push Not at hne
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hne y] at this
  simpa using this.symm

theorem im_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) (τ : E →+* ℂ) : (τ β).im ≠ 0 := by
  intro h0
  apply hβ
  apply τ.injective
  rw [h.2.2.2 τ β]
  exact Complex.conj_eq_iff_im.2 h0

theorem exists_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) :
    ∃ B : Module.Basis (Fin 2) F E, B 0 = 1 ∧ B 1 = β := by
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hβ
      have e : β = algebraMap F E (-(s / t)) := by
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_neg, map_div₀]
        field_simp
        linear_combination hst
      rw [e, AlgHom.commutes]
    subst ht
    simpa using hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h.2.2.1]), ?_, ?_⟩ <;> simp

omit [NumberField E] in
theorem eq_add_tmul (B : Module.Basis (Fin 2) F E) (x : AF F ⊗[F] E) :
    x = (Algebra.TensorProduct.basis (AF F) B).repr x 0 ⊗ₜ[F] B 0 +
      (Algebra.TensorProduct.basis (AF F) B).repr x 1 ⊗ₜ[F] B 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) B).sum_repr x]
  simp [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

omit [NumberField E] in
theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (y : E) :
    piInf τ (a ⊗ₜ[F] y) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 y := rfl

omit [NumberField F] in
theorem im_extension (hF : IsTotallyReal F) (w : InfinitePlace F) (z : w.Completion) :
    (InfinitePlace.Completion.extensionEmbedding w z).im = 0 := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) z]
  exact Complex.ofReal_im _

theorem piInf_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, star_add]
  | tmul a e =>
    show piInf τ (a ⊗ₜ[F] σ e) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul']
    congr 1
    exact (Complex.conj_eq_iff_im.2 (im_extension h.1 w _)).symm

omit [NumberField E] in
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  let φ : AF F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp (evInf F w : AF F →+* w.Completion)
  have hφ : Continuous φ := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)
  let : Algebra (AF F) ℂ := φ.toAlgebra
  have : ContinuousSMul (AF F) ℂ := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  let L : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := fun c y => by
        have : c • y = (c ⊗ₜ[F] (1 : E)) * y := by rw [Algebra.smul_def]; rfl
        rw [this, map_mul, piInf_tmul, map_one, mul_one]; rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem eq_zero_of_piInf {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (x : AE F E)
    (hx : At (evI F) x) (hinf : ∀ w, piInf (τ w) x = 0) : x = 0 := by
  obtain ⟨β, hβ⟩ := exists_moved h
  obtain ⟨B, hB0, hB1⟩ := exists_basis h hβ
  have hdec := eq_add_tmul B x
  set C := Algebra.TensorProduct.basis (AF F) B with hC
  have hu : pairA F 0 1 • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hfin : ∀ i, (C.repr x i).2 = 0 := fun i => by
    have h1 : C.repr (pairA F 0 1 • x) i = 0 := by rw [hu]; simp
    rw [map_smul] at h1
    have h2 : pairA F 0 1 * C.repr x i = 0 := h1
    have h3 := congrArg (sndA F) h2
    rw [map_mul, map_zero] at h3
    exact (one_mul _).symm.trans h3
  have hre : ∀ w i, (C.repr x i).1 w = 0 := fun w => by
    have e := hinf w
    rw [hdec, map_add, piInf_tmul, piInf_tmul, hB0, hB1, map_one, mul_one] at e
    have hi := congrArg Complex.im e
    have him := im_ne_zero h hβ (τ w).1
    set p := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 0).1 w) with hp
    set q := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 1).1 w) with hq
    have hpi : p.im = 0 := im_extension h.1 w _
    have hqi : q.im = 0 := im_extension h.1 w _
    simp only [Complex.add_im, Complex.mul_im, Complex.zero_im, hpi, hqi, zero_mul, add_zero, zero_add] at hi
    have hq0 : q.re = 0 := (mul_eq_zero.1 hi).resolve_right him
    have hq1 : q = 0 := Complex.ext hq0 hqi
    rw [hq1, zero_mul, add_zero] at e
    have inj := (InfinitePlace.Completion.extensionEmbedding w).injective
    intro i
    fin_cases i
    · show (C.repr x 0).1 w = 0
      exact inj (e.trans (map_zero _).symm)
    · show (C.repr x 1).1 w = 0
      exact inj (hq1.trans (map_zero _).symm)
  have hz : C.repr x = 0 := by
    ext i
    show C.repr x i = 0
    exact Prod.ext (funext fun w => hre w i) (hfin i)
  simpa using hz

def ofInf (c : ∀ w : InfinitePlace F, w.Completion) : AF F := ((c : Ainf F), (0 : Af F))

theorem continuous_ofInf : Continuous (ofInf (F := F)) := continuous_id.prodMk continuous_const

theorem mul_ofInf (u : AF F) (hu : evI F u = 0) (c : ∀ w : InfinitePlace F, w.Completion) : u * ofInf c = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem exists_section {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ ∀ z, At (evI F) (s z) ∧ ∀ w, piInf (τ w) (s z) = z w := by
  have hF := h.1
  obtain ⟨β, hβ⟩ := exists_moved h
  have him : ∀ w, ((τ w).1 β).im ≠ 0 := fun w => im_ne_zero h hβ _
  let e : ∀ w : InfinitePlace F, w.Completion ≃ᵢ ℝ := fun w =>
    InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  have he : ∀ w a, InfinitePlace.Completion.extensionEmbedding w a = ((e w a : ℝ) : ℂ) := fun w a =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) a).symm
  let s : (InfinitePlace F → ℂ) → InfinitePlace F → ℝ := fun z w => (z w).im / ((τ w).1 β).im
  let r : (InfinitePlace F → ℂ) → InfinitePlace F → ℝ := fun z w => (z w).re - s z w * ((τ w).1 β).re
  have hs : ∀ w, Continuous fun z => s z w := fun w => by fun_prop
  have hr : ∀ w, Continuous fun z => r z w := fun w => by fun_prop
  refine ⟨fun z => ofInf (fun w => (e w).symm (r z w)) • ((1 : AF F) ⊗ₜ[F] (1 : E)) +
    ofInf (fun w => (e w).symm (s z w)) • ((1 : AF F) ⊗ₜ[F] β), ?_, fun z => ⟨?_, fun w => ?_⟩⟩
  · have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
    have : ContinuousSMul (AF F) (AE F E) := inferInstance
    have c1 : Continuous fun z => ofInf (fun w => (e w).symm (r z w)) :=
      continuous_ofInf.comp (continuous_pi fun w => (e w).symm.continuous.comp (hr w))
    have c2 : Continuous fun z => ofInf (fun w => (e w).symm (s z w)) :=
      continuous_ofInf.comp (continuous_pi fun w => (e w).symm.continuous.comp (hs w))
    exact (c1.smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] (1 : E) : AE F E)))).add
      (c2.smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] β : AE F E))))
  · intro u hu
    rw [smul_add, smul_smul, smul_smul, mul_ofInf u hu, mul_ofInf u hu, zero_smul, zero_smul, add_zero]
  · have hc : ∀ (c : ∀ w : InfinitePlace F, w.Completion) (y : E),
        piInf (τ w) (ofInf c • ((1 : AF F) ⊗ₜ[F] y)) = ((e w (c w) : ℝ) : ℂ) * (τ w).1 y := fun c y => by
      rw [← he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    rw [map_add, hc, hc]
    simp only [(e w).apply_symm_apply, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, r]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, s]
      have := him w
      field_simp
      ring

variable {β : Type} [Fintype β] [DecidableEq β]

omit [Fintype β] [DecidableEq β] in

theorem mat_ext {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {X X' : Matrix β β (AE F E)}
    (hx : At (evI F) (X - X')) (hinf : ∀ w, X.map (piInf (τ w)) = X'.map (piInf (τ w))) : X = X' := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf h τ _ (fun u hu => congrFun (congrFun (hx u hu) i) j) fun w => ?_)
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun (hinf w) i) j

omit [DecidableEq β] in

theorem map_form {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (g J : Matrix β β (AE F E)) :
    (gᵀ * J * g.map (cA σ)).map (piInf τ) = (g.map (piInf τ))ᵀ * J.map (piInf τ) * (g.map (piInf τ)).map star := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  congr 1
  ext i j
  exact piInf_cA h τ _

end Adele

theorem genEx : GlobalTheory.RealLift.GenEx := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC γ hγ
  have key : ∀ w, ∃ Y : Mat R S, Y ∈ upq R S ∧ ∀ t : ℝ,
      ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
        C w * NormedSpace.exp (t • Y) := fun w => by
    obtain ⟨C', h1, h2⟩ := frame_inv (hC w)
    let g : ℝ → Matrix β β ℂ := fun t => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w))
    have hg : Continuous g :=
      ((Units.continuous_val.comp continuous_subtype_val).comp (hγ.1.comp continuous_ofAdd)).matrix_map
        (continuous_piInf (τ w))
    have hg0 : g 0 = 1 := by
      simp only [g, ofAdd_zero, map_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hgm : ∀ s t, g (s + t) = g s * g t := fun s t => by
      simp only [g, ofAdd_add, map_mul]
      exact Matrix.map_mul
    have hgC : ∀ t, g t * C w = C w * (C' * g t * C w) := fun t => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    obtain ⟨Y, hY, hA⟩ := exists_gen_matrix (fun t => C' * g t * C w)
      ((continuous_const.matrix_mul hg).matrix_mul continuous_const)
      (by rw [hg0, Matrix.mul_one, h2])
      (fun s t => by
        rw [hgm, Matrix.mul_assoc C' (g s), Matrix.mul_assoc C' (g s * C w), Matrix.mul_assoc (g s) (C w), ← hgC]
        simp only [Matrix.mul_assoc])
      (Jm R S) fun t => (frame_iff_smul (hC w) (hgC t)).1 (by
        rw [← map_form hcm]
        exact congrArg (fun X : Matrix β β (AE F E) => X.map (piInf (τ w))) (γ (Multiplicative.ofAdd t)).2)
    exact ⟨Y, hY, fun t => by rw [← hA t]; exact hgC t⟩
  choose Y hY hgen using key
  exact ⟨Y, hY, fun t w => hgen w t⟩

theorem lineEx : GlobalTheory.RealLift.LineEx := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC Y hY
  obtain ⟨s, hs, hs'⟩ := exists_section hcm τ
  choose C' h1 h2 using fun w => frame_inv (hC w)
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  let g : InfinitePlace F → ℝ → Matrix β β ℂ := fun w t => C w * NormedSpace.exp (t • Y w) * C' w
  have hg : ∀ w, Continuous (g w) := fun w =>
    (continuous_const.matrix_mul (continuous_exp_smul (Y w))).matrix_mul continuous_const
  have hgC : ∀ w t, g w t * C w = C w * NormedSpace.exp (t • Y w) := fun w t => by
    simp only [g]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  let N : ℝ → Matrix β β (AE F E) := fun t => Matrix.of fun i j => s fun w => (g w t - 1) i j
  have hN : ∀ t u, evI F u = 0 → u • N t = 0 := fun t u hu => by
    ext i j
    exact (hs' _).1 u hu
  have hNc : Continuous N := continuous_matrix fun i j => hs.comp (continuous_pi fun w =>
    ((hg w).sub continuous_const).matrix_elem i j)
  let G : ℝ → Matrix β β (AE F E) := fun t => 1 + N t
  have hGc : Continuous G := continuous_const.add hNc
  have hG : ∀ t w, (G t).map (piInf (τ w)) = g w t := fun t w => by
    have e : (N t).map (piInf (τ w)) = g w t - 1 := by
      ext i j
      exact (hs' _).2 w
    simp only [G]
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), e, add_sub_cancel]
  have hG0 : G 0 = 1 := mat_ext hcm τ (fun u hu => by simp only [G, add_sub_cancel_left]; exact hN 0 u hu) fun w => by
    rw [hG, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [g, h1]
  have hGm : ∀ a c, G (a + c) = G a * G c := fun a c => by
    refine mat_ext hcm τ (fun u hu => ?_) fun w => ?_
    · have e : G (a + c) - G a * G c = N (a + c) - N c - N a * G c := by
        simp only [G]
        noncomm_ring
      rw [e, smul_sub, smul_sub, ← Matrix.smul_mul, hN _ u hu, hN _ u hu, hN _ u hu]
      simp
    · rw [Matrix.map_mul, hG, hG, hG]
      conv_rhs => rw [show g w c = C w * NormedSpace.exp (c • Y w) * C' w from rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hgC, Matrix.mul_assoc (C w), ← exp_add_smul]
  have hGU : ∀ t, (G t)ᵀ * J * (G t).map (cA σ) = J := fun t => by
    refine mat_ext hcm τ (fun u hu => ?_) fun w => ?_
    · have e0 : (G t).map (cA σ) = 1 + (N t).map (cA σ) := by
        simp only [G]
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      have e : (G t)ᵀ * J * (G t).map (cA σ) - J = (N t)ᵀ * (J * (G t).map (cA σ)) + J * (N t).map (cA σ) := by
        rw [e0]
        simp only [G, Matrix.transpose_add, Matrix.transpose_one]
        noncomm_ring
      have e1 : u • (N t).map (cA σ) = 0 := by
        ext i j
        have := congrArg (cA σ) (congrFun (congrFun (hN t u hu) i) j)
        simpa using this
      rw [e, smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, e1, ← Matrix.transpose_smul, hN t u hu]
      simp
    · rw [map_form hcm, hG]
      refine (frame_iff_smul (hC w) (hgC w t)).2 (exp_preserves ?_)
      have hY' : (Y w)ᴴ * Jm R S + Jm R S * Y w = 0 := hY w
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY', smul_zero]
  let U : ℝ → GL β (AE F E) := fun t =>
    ⟨G t, G (-t), by rw [← hGm, add_neg_cancel, hG0], by rw [← hGm, neg_add_cancel, hG0]⟩
  have hU : Continuous U := Units.continuous_iff.2 ⟨hGc, hGc.comp continuous_neg⟩
  let γ : Multiplicative ℝ →* UG (cA σ) J :=
    { toFun := fun t => ⟨U t.toAdd, hGU _⟩
      map_one' := Subtype.ext (Units.ext hG0)
      map_mul' := fun a c => Subtype.ext (Units.ext (hGm _ _)) }
  refine ⟨γ, ⟨(hU.comp continuous_toAdd).subtype_mk _, fun t u hu => ?_⟩, fun t w => ?_⟩
  · show u • (1 + N t.toAdd - 1) = 0
    rw [add_sub_cancel_left, hN _ u hu]
  · show (G t).map (piInf (τ w)) * C w = _
    rw [hG, hgC]

theorem kLine : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := by
  intro hL F E _ _ _ _ _ σ β _ _ R S τ J b C θ hcm hC hθ k hk hkθ
  choose C' h1 h2 using fun w => frame_inv (hC w)
  have key : ∀ w, ∃ Y : Mat R S, Y ∈ upq R S ∧ IsKC Y ∧
      (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * NormedSpace.exp Y := fun w => by
    set g := (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hgdef
    obtain ⟨h, hg⟩ : ∃ h : Mat R S, g * C w = C w * h :=
      ⟨C' w * g * C w, by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]⟩
    have hf : hᴴ * Jm R S * h = Jm R S := (frame_iff_smul (hC w) hg).1 (by
      rw [hgdef, ← map_form hcm]
      exact congrArg (fun X : Matrix β β (AE F E) => X.map (piInf (τ w))) k.2)
    have hc : Commute h (Jm R S) := by
      have e : C w * (h * Jm R S) = C w * (Jm R S * h) := by
        rw [← Matrix.mul_assoc, ← hg, Matrix.mul_assoc, ← hθ, ← Matrix.mul_assoc, (hkθ w).eq, Matrix.mul_assoc, hg,
          ← Matrix.mul_assoc, hθ, Matrix.mul_assoc]
      have e' := congrArg (fun X => C' w * X) e
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul] at e'
      exact e'
    have hu : hᴴ * h = 1 := by
      rw [Matrix.mul_assoc, ← hc.eq, ← Matrix.mul_assoc] at hf
      rw [← Matrix.mul_one (hᴴ * h), ← Jm_mul_self, ← Matrix.mul_assoc, hf]
    obtain ⟨Y, hY, hYc, hYe⟩ := exists_log_unitary hu Jm_conjTranspose hc
    refine ⟨Y, ?_, isKC_of_commute hYc, by rw [hYe, hg]⟩
    show Yᴴ * Jm R S + Jm R S * Y = 0
    rw [hY, Matrix.neg_mul, hYc.eq, neg_add_cancel]
  choose Y hY hK hkY using key
  obtain ⟨γ, hγ, hgen⟩ := hL F E σ β R S τ J b C hcm hC Y hY
  refine ⟨γ, hγ, Y, hgen, hK, Subtype.ext (Units.ext (mat_ext hcm τ (fun u hu => ?_) fun w => ?_))⟩
  · rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, hγ.2 _ u hu, hk u hu, sub_zero]
  · have e := hgen 1 w
    rw [one_smul, ← hkY] at e
    have e' := congrArg (fun X => X * C' w) e
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at e'
    exact e'

end PositivityTheory.RL

end
