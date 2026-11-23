import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFrame

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace PositivityTheory.ThKF.Cart

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

theorem conj_mat {n r s : ℕ} {M θ θ₂ : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h1 : IsCartan M θ) (h2 : IsCartan M θ₂) :
    ∃ g g' : Matrix (Fin n) (Fin n) ℂ, g * g' = 1 ∧ gᵀ * M * g.map star = M ∧ g * θ₂ = θ * g := by
  obtain ⟨A, hA, eA⟩ := PositivityTheory.RL.frameEx n r s M θ h h1
  obtain ⟨C, hC, eC⟩ := PositivityTheory.RL.frameEx n r s M θ₂ h h2
  obtain ⟨A', a1, -⟩ := frame_inv hA
  obtain ⟨C', c1, c2⟩ := frame_inv hC
  refine ⟨A * C', C * A', ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C', c2, Matrix.one_mul, a1]
  · calc (A * C')ᵀ * M * (A * C').map star = C'ᵀ * (Aᵀ * M * A.map star) * C'.map star := by
          simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = (C * C')ᵀ * M * (C * C').map star := by
          rw [hA.1, ← hC.1]
          simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = M := by rw [c1, map_star_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  · have e : θ₂ = C * Jm r s * C' := by rw [← eC, Matrix.mul_assoc, c1, Matrix.mul_one]
    rw [← Matrix.mul_assoc θ, eA, e]
    calc A * C' * (C * Jm r s * C') = A * (C' * C) * Jm r s * C' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c2, Matrix.mul_one]

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

theorem exists_mat {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : InfinitePlace F → Matrix β β ℂ) :
    ∃ N : Matrix β β (AE F E), At (evI F) N ∧ ∀ w, (1 + N).map (piInf (τ w)) = g w := by
  obtain ⟨s, -, hs'⟩ := exists_section hcm τ
  refine ⟨Matrix.of fun i j => s fun w => (g w - 1) i j, fun u hu => ?_, fun w => ?_⟩
  · ext i j
    exact (hs' _).1 u hu
  · have e : (Matrix.of fun i j => s fun w => (g w - 1) i j).map (piInf (τ w)) = g w - 1 := by
      ext i j
      exact (hs' _).2 w
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), e, add_sub_cancel]

theorem exists_point {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E))
    (g g' : InfinitePlace F → Matrix β β ℂ) (hi : ∀ w, g w * g' w = 1)
    (hu : ∀ w, (g w)ᵀ * J.map (piInf (τ w)) * (g w).map star = J.map (piInf (τ w))) :
    ∃ x : UG (cA σ) J, At (evI F) ((x.1 : Matrix β β (AE F E)) - 1) ∧ ∀ w, (x.1 : Matrix β β (AE F E)).map (piInf (τ w)) = g w := by
  obtain ⟨N, hN, hG⟩ := exists_mat hcm τ g
  obtain ⟨N', hN', hG'⟩ := exists_mat hcm τ g'
  have hm : (1 + N) * (1 + N') = 1 := by
    refine mat_ext hcm τ (fun u hu => ?_) fun w => ?_
    · have e : (1 + N) * (1 + N') - 1 = N' + N * (1 + N') := by noncomm_ring
      rw [e, smul_add, ← Matrix.smul_mul, hN _ hu, hN' _ hu]
      simp
    · rw [Matrix.map_mul, hG, hG', hi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hU : (1 + N)ᵀ * J * (1 + N).map (cA σ) = J := by
    refine mat_ext hcm τ (fun u hu => ?_) fun w => ?_
    · have e0 : (1 + N).map (cA σ) = 1 + N.map (cA σ) := by
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      have e : (1 + N)ᵀ * J * (1 + N).map (cA σ) - J = Nᵀ * (J * (1 + N).map (cA σ)) + J * N.map (cA σ) := by
        rw [e0]
        simp only [Matrix.transpose_add, Matrix.transpose_one]
        noncomm_ring
      have e1 : u • N.map (cA σ) = 0 := by
        ext i j
        have := congrArg (cA σ) (congrFun (congrFun (hN u hu) i) j)
        simpa using this
      rw [e, smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, e1, ← Matrix.transpose_smul, hN u hu]
      simp
    · rw [map_form hcm, hG, hu]
  refine ⟨⟨⟨1 + N, 1 + N', hm, mul_eq_one_comm.1 hm⟩, hU⟩, fun u hu => ?_, hG⟩
  show u • (1 + N - 1) = 0
  rw [add_sub_cancel_left, hN _ hu]

theorem incM_piInf {m : ℕ} {w : InfinitePlace F} (τ : EmbOver E w) (J : Matrix (Fin m) (Fin m) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  show piInf τ ((1 : AF F) ⊗ₜ[F] J i j) = _
  rw [piInf_tmul]
  show InfinitePlace.Completion.extensionEmbedding w 1 * _ = _
  rw [map_one, one_mul]
  rfl

theorem exists_conj {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m r s : ℕ} (Y : Spc F E m)
    (c : ℂ) (hc : c ≠ 0) (θ₂ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ) (hs : ∀ w, HasSig (c • Y.J.map (τ w).1) r s)
    (h1 : ∀ w, IsCartan (c • Y.J.map (τ w).1) (Y.θ w)) (h2 : ∀ w, IsCartan (c • Y.J.map (τ w).1) (θ₂ w)) :
    ∃ h ∈ UAt σ Y (evI F), ∀ w, (mat h).map (piInf (τ w)) * θ₂ w = Y.θ w * (mat h).map (piInf (τ w)) := by
  choose g g' a1 a2 a3 using fun w => conj_mat (hs w) (h1 w) (h2 w)
  obtain ⟨x, hx, e⟩ := exists_point hcm τ (incM F Y.J) g g' a1 fun w => by
    have := a2 w
    rw [Matrix.mul_smul, Matrix.smul_mul] at this
    rw [incM_piInf]
    exact smul_right_injective _ hc this
  exact ⟨x, hx, fun w => by rw [show (mat x).map (piInf (τ w)) = g w from e w, a3]⟩

end Adele

end PositivityTheory.ThKF.Cart

end
