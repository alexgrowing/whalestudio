import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift.OneParam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def liftR [IsTotallyReal F] (r : InfinitePlace F → ℝ) : AF F :=
  LinearMap.inl F (Ainf F) (Af F)
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (r w))

theorem evInf_liftR [IsTotallyReal F] (r : InfinitePlace F → ℝ) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (liftR r)) = r w := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  change ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w))
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (r w)) : ℂ) = r w
  congr 1
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (r w)

theorem continuous_liftR [IsTotallyReal F] : Continuous (liftR (F := F)) := by
  have h : ∀ w : InfinitePlace F, Continuous (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm :=
    fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous
  exact Continuous.prodMk (continuous_pi fun w => (h w).comp (continuous_apply w)) continuous_const

end GlobalTheory.RealLift.OneParam

namespace GlobalTheory.RealLift.OneParam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ξ : E, σ ξ ≠ ξ := by
  by_contra hc
  push Not at hc
  have := h.2.1
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
  change star (τ x) = τ x
  rw [← h.2.2.2 τ x, hc x]

theorem im_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {ξ : E} (hξ : σ ξ ≠ ξ) (τ : E →+* ℂ) : (τ ξ).im ≠ 0 := by
  intro h0
  apply hξ
  apply τ.injective
  rw [h.2.2.2 τ ξ]
  exact Complex.conj_eq_iff_im.2 h0

def liftC [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E) (c : InfinitePlace F → ℂ) : AE F E :=
  liftR (fun w => (c w).re - (c w).im / ((τ w).1 ξ).im * ((τ w).1 ξ).re) ⊗ₜ[F] (1 : E) +
    liftR (fun w => (c w).im / ((τ w).1 ξ).im) ⊗ₜ[F] ξ

theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (e : E) :
    piInf τ (a ⊗ₜ[F] e) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) * τ.1 e := rfl

theorem piInf_liftC [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E} (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0)
    (c : InfinitePlace F → ℂ) (w : InfinitePlace F) : piInf (τ w) (liftC τ ξ c) = c w := by
  rw [liftC, map_add, piInf_tmul, piInf_tmul, evInf_liftR, evInf_liftR, map_one, mul_one]
  have := hξ w
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem continuous_liftC [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E) :
    Continuous (liftC τ ξ) := by
  have ht : ∀ e : E, Continuous fun a : AF F => a ⊗ₜ[F] e := fun e => by
    have : (fun a : AF F => a ⊗ₜ[F] e) = fun a => a • ((1 : AF F) ⊗ₜ[F] e) := funext fun a => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact (continuous_id (X := AF F)).smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] e)))
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine ((ht 1).comp (continuous_liftR.comp ?_)).add ((ht ξ).comp (continuous_liftR.comp ?_))
  · exact continuous_pi fun w => (Complex.continuous_re.comp (continuous_apply w)).sub
      (((Complex.continuous_im.comp (continuous_apply w)).div_const _).mul continuous_const)
  · exact continuous_pi fun w => (Complex.continuous_im.comp (continuous_apply w)).div_const _

theorem inf_eq_zero {u : AF F} (hu : evI F u = 0) : u.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)

theorem mul_liftR [IsTotallyReal F] {u : AF F} (hu : evI F u = 0) (r : InfinitePlace F → ℝ) : u * liftR r = 0 := by
  have h1 := inf_eq_zero hu
  refine Prod.ext ?_ ?_
  · change u.1 * (liftR r).1 = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem at_liftC [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E) (c : InfinitePlace F → ℂ) :
    At (evI F) (liftC τ ξ c) := fun u hu => by
  rw [liftC, smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_liftR hu, mul_liftR hu, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]

theorem piInf_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = starRingEnd ℂ (piInf τ z) := by
  have := h.1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    rw [cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, piInf_tmul, piInf_tmul, map_mul,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w), Complex.conj_ofReal]
    congr 1
    exact h.2.2.2 τ.1 e
end GlobalTheory.RealLift.OneParam

namespace GlobalTheory.RealLift.OneParam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem linInd_one {σ : E →ₐ[F] E} {ξ : E} (hξ : σ ξ ≠ ξ) : LinearIndependent F ![(1 : E), ξ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right one_ne_zero, rfl⟩
  · exfalso
    apply hξ
    have e : ξ = algebraMap F E (-(s / t)) := by
      rw [Algebra.algebraMap_eq_smul_one]
      have : t • ξ = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      calc ξ = t⁻¹ • (t • ξ) := (inv_smul_smul₀ ht ξ).symm
        _ = _ := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    rw [e, AlgHom.commutes]

theorem eq_zero_of_at {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {z : AE F E} (hz : At (evI F) z) (h0 : ∀ w, piInf (τ w) z = 0) : z = 0 := by
  have := h.1
  obtain ⟨ξ, hξ⟩ := exists_moved h
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let bE := basisOfLinearIndependentOfCardEqFinrank (linInd_one hξ) hcard
  let B := Algebra.TensorProduct.basis (AF F) bE
  have hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] ![(1 : E), ξ] i := fun i => by
    simp [B, bE, Algebra.TensorProduct.basis_apply]
  set a := B.repr z with ha_def
  have hz' : z = a 0 ⊗ₜ[F] (1 : E) + a 1 ⊗ₜ[F] ξ := by
    conv_lhs => rw [← B.sum_repr z]
    rw [Fin.sum_univ_two, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
      mul_one, mul_one]
    rfl
  let u : AF F := LinearMap.inr F (Ainf F) (Af F) 1
  have hu : evI F u = 0 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  have hfin : ∀ i, u * a i = 0 := fun i => by
    have e := congrArg (fun y => B.repr y i) (hz u hu)
    simpa [ha_def] using e
  have hinf : ∀ w, evInf F w (a 0) = 0 ∧ evInf F w (a 1) = 0 := fun w => by
    have e := h0 w
    rw [hz', map_add, piInf_tmul, piInf_tmul, map_one, mul_one,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)] at e
    set x := InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (evInf F w (a 0)) with hx
    set y := InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (evInf F w (a 1)) with hy
    have hne := im_ne_zero h hξ (τ w).1
    have him := congrArg Complex.im e
    have hre := congrArg Complex.re e
    simp at him hre
    have y0 : y = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 hne
    rw [y0, zero_mul, add_zero] at hre
    constructor
    · exact (map_eq_zero _).1 (hx ▸ hre)
    · exact (map_eq_zero _).1 (hy ▸ y0)
  have ha : ∀ i, a i = 0 := fun i => by
    refine Prod.ext ?_ ?_
    · funext w
      change evInf F w (a i) = 0
      fin_cases i
      · exact (hinf w).1
      · exact (hinf w).2
    · have e := congrArg Prod.snd (hfin i)
      change (1 : Af F) * (a i).2 = 0 at e
      rw [one_mul] at e
      exact e
  rw [hz', ha 0, ha 1, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
end GlobalTheory.RealLift.OneParam

namespace GlobalTheory.RealLift.OneParam
open scoped Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {β : Type} [Fintype β] [DecidableEq β]

theorem at_sub {X Y : Matrix β β (AE F E)} (hX : At (evI F) X) (hY : At (evI F) Y) : At (evI F) (X - Y) :=
  fun u hu => by rw [smul_sub, hX u hu, hY u hu, sub_zero]

theorem at_add {X Y : Matrix β β (AE F E)} (hX : At (evI F) X) (hY : At (evI F) Y) : At (evI F) (X + Y) :=
  fun u hu => by rw [smul_add, hX u hu, hY u hu, add_zero]

theorem at_mul_right {X : Matrix β β (AE F E)} (hX : At (evI F) X) (Y : Matrix β β (AE F E)) : At (evI F) (X * Y) :=
  fun u hu => by rw [← Matrix.smul_mul, hX u hu, Matrix.zero_mul]

theorem at_mul_left {X : Matrix β β (AE F E)} (hX : At (evI F) X) (Y : Matrix β β (AE F E)) : At (evI F) (Y * X) :=
  fun u hu => by rw [← Matrix.mul_smul, hX u hu, Matrix.mul_zero]

theorem at_transpose {X : Matrix β β (AE F E)} (hX : At (evI F) X) : At (evI F) Xᵀ :=
  fun u hu => by rw [← Matrix.transpose_smul, hX u hu, Matrix.transpose_zero]

theorem at_map_cA (σ : E →ₐ[F] E) {X : Matrix β β (AE F E)} (hX : At (evI F) X) : At (evI F) (X.map (cA σ)) :=
  fun u hu => by
    have e := hX u hu
    ext i j
    have e' := congrFun (congrFun e i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply] at e' ⊢
    rw [Matrix.map_apply, ← map_smul, e', map_zero]

theorem eq_of_at {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {X Y : Matrix β β (AE F E)} (hXY : At (evI F) (X - Y)) (hw : ∀ w, X.map (piInf (τ w)) = Y.map (piInf (τ w))) :
    X = Y := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_at h τ (fun u hu => ?_) fun w => ?_)
  · have e := congrFun (congrFun (hXY u hu) i) j
    simpa using e
  · have e := congrFun (congrFun (hw w) i) j
    simp only [Matrix.map_apply] at e
    rw [map_sub, e, sub_self]

def liftM [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E) (M : InfinitePlace F → Matrix β β ℂ) :
    Matrix β β (AE F E) :=
  Matrix.of fun i j => liftC τ ξ fun w => M w i j

theorem liftM_map [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E} (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0)
    (M : InfinitePlace F → Matrix β β ℂ) (w : InfinitePlace F) : (liftM τ ξ M).map (piInf (τ w)) = M w := by
  ext i j
  exact piInf_liftC τ hξ _ w

theorem at_liftM [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E)
    (M : InfinitePlace F → Matrix β β ℂ) : At (evI F) (liftM τ ξ M) := fun u hu => by
  ext i j
  exact at_liftC τ ξ _ u hu

theorem continuous_liftM [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E) :
    Continuous (liftM (β := β) τ ξ) :=
  continuous_matrix fun i j => (continuous_liftC τ ξ).comp
    (continuous_pi fun w => ((continuous_apply w).matrix_elem i j))

end GlobalTheory.RealLift.OneParam

namespace GlobalTheory.RealLift.OneParam
open scoped Matrix
variable {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ}

theorem jm_mul_self : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem jm_transpose : (Jm R S)ᵀ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem frame_inv {M : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} {C' : Matrix (Ix R S) β ℂ}
    (hF : Cᵀ * M * C.map star = Jm R S) (hR : C * C' = 1) : C' * C = 1 := by
  have hs : ∀ {m n : Type} (A : Matrix m n ℂ), A.map star = A.map (starRingEnd ℂ) := fun _ => rfl
  set D := C.map (starRingEnd ℂ)
  set D' := C'.map (starRingEnd ℂ)
  have h1 : (Jm R S * Cᵀ * M) * D = 1 := by
    change Jm R S * Cᵀ * M * C.map star = 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Cᵀ, hF, jm_mul_self]
  have h2 : D * D' = 1 := by
    rw [← Matrix.map_mul, hR, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : Jm R S * Cᵀ * M = D' := by
    calc Jm R S * Cᵀ * M = (Jm R S * Cᵀ * M) * (D * D') := by rw [h2, Matrix.mul_one]
      _ = D' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h4 : D' * D = 1 := by rw [← h3, h1]
  have h5 : (C' * C).map (starRingEnd ℂ) = 1 := by rw [Matrix.map_mul]; exact h4
  have h6 := congrArg (fun A => A.map (starRingEnd ℂ)) h5
  simp only [Matrix.map_map, Matrix.map_one _ (map_zero _) (map_one _)] at h6
  convert h6 using 1
  ext i j
  simp

theorem exp_unitary {Y : Mat R S} (hY : Y ∈ upq R S) (t : ℝ) :
    (NormedSpace.exp (t • Y))ᵀ * Jm R S * (NormedSpace.exp (t • Y)).map star = Jm R S := by
  have hYh : Yᴴ = Jm R S * (-Y) * Jm R S := by
    have e : Yᴴ * Jm R S + Jm R S * Y = 0 := hY
    have e2 : Yᴴ = -(Jm R S * Y) * Jm R S := by
      have := congrArg (· * Jm R S) (eq_neg_of_add_eq_zero_left e)
      simpa [Matrix.mul_assoc, jm_mul_self] using this
    rw [e2, Matrix.mul_neg, Matrix.neg_mul]
  have hu : IsUnit (Jm R S) := ⟨⟨Jm R S, Jm R S, jm_mul_self, jm_mul_self⟩, rfl⟩
  have hinv : (Jm R S)⁻¹ = Jm R S := Matrix.inv_eq_left_inv jm_mul_self
  have hH : (NormedSpace.exp (t • Y))ᴴ = Jm R S * NormedSpace.exp (-(t • Y)) * Jm R S := by
    have key : t • Yᴴ = Jm R S * (-(t • Y)) * (Jm R S)⁻¹ := by
      rw [hinv, hYh, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.mul_smul,
        Matrix.smul_mul]
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial, key, Matrix.exp_conj _ _ hu, hinv]
  have hU : (NormedSpace.exp (t • Y))ᴴ * Jm R S * NormedSpace.exp (t • Y) = Jm R S := by
    rw [hH, Matrix.mul_assoc _ (Jm R S) (Jm R S), jm_mul_self, Matrix.mul_one, Matrix.mul_assoc,
      ← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • Y)).neg_left), neg_add_cancel, NormedSpace.exp_zero,
      Matrix.mul_one]
  have := congrArg Matrix.transpose hU
  rw [Matrix.transpose_mul, Matrix.transpose_mul, jm_transpose, Matrix.conjTranspose, Matrix.transpose_map,
    Matrix.transpose_transpose]
    at this
  rw [← Matrix.mul_assoc] at this
  exact this

end GlobalTheory.RealLift.OneParam

namespace GlobalTheory.RealLift.OneParam
open scoped Matrix
variable {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ}

theorem map_star_mul {m n p : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem conj_add {C : Matrix β (Ix R S) ℂ} {C' : Matrix (Ix R S) β ℂ} (hL : C' * C = 1) (Y : Mat R S) (s t : ℝ) :
    C * NormedSpace.exp ((s + t) • Y) * C' =
      (C * NormedSpace.exp (s • Y) * C') * (C * NormedSpace.exp (t • Y) * C') := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc C' C, hL, Matrix.one_mul]

theorem conj_zero {C : Matrix β (Ix R S) ℂ} {C' : Matrix (Ix R S) β ℂ} (hR : C * C' = 1) (Y : Mat R S) :
    C * NormedSpace.exp ((0 : ℝ) • Y) * C' = 1 := by
  rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one, hR]

theorem conj_unitary {N : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} {C' : Matrix (Ix R S) β ℂ}
    (hF : Cᵀ * N * C.map star = Jm R S) (hR : C * C' = 1) {Y : Mat R S} (hY : Y ∈ upq R S) (t : ℝ) :
    (C * NormedSpace.exp (t • Y) * C')ᵀ * N * (C * NormedSpace.exp (t • Y) * C').map star = N := by
  set X := NormedSpace.exp (t • Y)
  have hX := exp_unitary hY t
  calc (C * X * C')ᵀ * N * (C * X * C').map star
        = C'ᵀ * (Xᵀ * (Cᵀ * N * C.map star) * X.map star) * C'.map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = C'ᵀ * (Cᵀ * N * C.map star) * C'.map star := by rw [hF, hX, ← hF]
      _ = (C * C')ᵀ * N * (C * C').map star := by
          rw [map_star_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = N := by
          rw [hR, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (by simp) (by simp), Matrix.mul_one]

theorem isEmpty_of_zero {M : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} {C' : Matrix (Ix R S) β ℂ}
    (hF : Cᵀ * ((0 : ℂ) • M) * C.map star = Jm R S) (hR : C * C' = 1) : IsEmpty β := by
  rw [zero_smul, Matrix.mul_zero, Matrix.zero_mul] at hF
  have hI : IsEmpty (Ix R S) := by
    refine ⟨fun a => ?_⟩
    have e := congrFun (congrFun hF a) a
    cases a <;> simp [Jm, Formalism.UG.Jpq] at e
  refine ⟨fun i => ?_⟩
  have e := congrFun (congrFun hR i) i
  simp [Matrix.mul_apply] at e

end GlobalTheory.RealLift.OneParam

namespace GlobalTheory.RealLift.OneParam
open scoped Matrix

theorem continuous_exp_smul {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (Matrix ι ι ℂ)
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end GlobalTheory.RealLift.OneParam

namespace GlobalTheory.RealLift
open scoped Matrix
open GlobalTheory.RealLift.OneParam

theorem exists_line_of_upq : LineEx := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC Y hY
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  set G : InfinitePlace F → ℝ → Matrix β β ℂ := fun w t => C w * NormedSpace.exp (t • Y w) * C' w with hG
  set f : ℝ → Matrix β β (AE F E) := fun t => 1 + liftM τ ξ (fun w => G w t - 1) with hf
  have hfπ : ∀ t w, (f t).map (piInf (τ w)) = G w t := fun t w => by
    rw [hf, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have hfat : ∀ t, At (evI F) (f t - 1) := fun t => by
    rw [hf, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have hfadd : ∀ s t, f (s + t) = f s * f t := fun s t => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : f s * f t - f (s + t) = (f s - 1) * f t + (f t - 1) - (f (s + t) - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (hfat s) _) (hfat t)) (hfat _)
    · rw [Matrix.map_mul, hfπ, hfπ, hfπ]
      exact (conj_add (hL w) (Y w) s t).symm
  have hf0 : f 0 = 1 := by
    refine eq_of_at hCM τ (hfat 0) fun w => ?_
    rw [hfπ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact conj_zero (hC' w) (Y w)
  have hfU : ∀ t, (f t)ᵀ * J * (f t).map (cA σ) = J := fun t => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (f t)ᵀ * J * (f t).map (cA σ) - J =
          (f t - 1)ᵀ * J * (f t).map (cA σ) + J * (f t - 1).map (cA σ) := by
        have e1 : (f t - 1).map (cA σ) = (f t).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (hfat t)) _) _)
        (at_mul_left (at_map_cA σ (hfat t)) _)
    · have hc : ((f t).map (cA σ)).map (piInf (τ w)) = (G w t).map star := by
        rw [← hfπ t w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, hfπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unitary (hC w).1 (hC' w) (hY w) t
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have hfc : Continuous f :=
    continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
      (((continuous_const.matrix_mul (continuous_exp_smul (Y w))).matrix_mul continuous_const).sub continuous_const)))
  let g : ℝ → UG (cA σ) J := fun t => ⟨⟨f t, f (-t), by rw [← hfadd, add_neg_cancel, hf0],
    by rw [← hfadd, neg_add_cancel, hf0]⟩, hfU t⟩
  let γ : Multiplicative ℝ →* UG (cA σ) J :=
    { toFun := fun t => g (Multiplicative.toAdd t)
      map_one' := Subtype.ext (Units.ext hf0)
      map_mul' := fun x y => Subtype.ext (Units.ext (hfadd _ _)) }
  refine ⟨γ, ⟨?_, fun t => hfat _⟩, fun t w => ?_⟩
  · have hu : Continuous fun t : Multiplicative ℝ => ((g (Multiplicative.toAdd t)).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨hfc.comp continuous_toAdd, (hfc.comp continuous_neg).comp continuous_toAdd⟩
    exact hu.subtype_mk _
  · change (f t).map (piInf (τ w)) * C w = C w * NormedSpace.exp (t • Y w)
    rw [hfπ, hG]
    simp only [Matrix.mul_assoc]
    rw [hL, Matrix.mul_one]

end GlobalTheory.RealLift
