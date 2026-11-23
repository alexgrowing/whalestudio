import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DeterminantCauchySchwarz
import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut

open NumberField GlobalTheory.AllWt Module TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SlopeExt

theorem card_tensor (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    {M : Type} [AddCommGroup M] [Module (𝓞 K) M] (h : IsFiniteLength (𝓞 K) M) :
    Nat.card (𝓞 K' ⊗[𝓞 K] M) = Nat.card M ^ finrank K K' := by
  induction h with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    have hinj : Function.Injective (N.subtype.lTensor (𝓞 K')) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range (N.subtype.lTensor (𝓞 K')))
    have h2 : Nat.card (LinearMap.range (N.subtype.lTensor (𝓞 K'))) = Nat.card (𝓞 K' ⊗[𝓞 K] N) :=
      (Nat.card_congr (LinearEquiv.ofInjective _ hinj).toEquiv).symm
    have h3 : Nat.card ((𝓞 K' ⊗[𝓞 K] M) ⧸ LinearMap.range (N.subtype.lTensor (𝓞 K'))) =
        Nat.card (𝓞 K' ⊗[𝓞 K] (M ⧸ N)) :=
      (Nat.card_congr (TensorProduct.tensorQuotientEquiv (𝓞 K') N).toEquiv).symm
    obtain ⟨p, -, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    have h4 : Nat.card (𝓞 K' ⊗[𝓞 K] (M ⧸ N)) = Nat.card (M ⧸ N) ^ finrank K K' := by
      rw [Nat.card_congr (LinearEquiv.lTensor (𝓞 K') e).toEquiv, Nat.card_congr e.toEquiv,
        ← Nat.card_congr (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (𝓞 K') p).toEquiv,
        ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← Ideal.absNorm_apply,
        Ideal.absNorm_algebraMap, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 K') K']
    rw [h1, h2, h3, h4, ih, Submodule.card_eq_card_quotient_mul_card N, mul_pow]

theorem relIndex_span {R S M W : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W]
    (l : M →ₗ[R] W) {j : ℕ} (e : Fin j → M) (he : LinearIndependent S fun k => l (e k)) (m : R)
    (hm : ∀ x : M, m • x = 0 → x = 0) (hme : ∀ x : M, m • x ∈ Submodule.span R (Set.range e)) :
    (Submodule.span S (Set.range fun k => l (e k))).toAddSubgroup.relIndex
        (Submodule.span S (Set.range l)).toAddSubgroup =
      Nat.card (S ⊗[R] (M ⧸ Submodule.span R (Set.range e))) := by
  set N := Submodule.span R (Set.range e) with hN
  set θ := l.liftBaseChange S with hθ
  have hP : N.baseChange S = Submodule.span S (Set.range fun k => (1 : S) ⊗ₜ[R] e k) := by
    rw [hN, Submodule.baseChange_span, ← Set.range_comp]; rfl
  have hmz : ∀ z : S ⊗[R] M, m • z ∈ N.baseChange S := fun z => by
    induction z with
    | zero => simp
    | tmul a x => rw [← tmul_smul]; exact Submodule.tmul_mem_baseChange_of_mem a (hme x)
    | add x y hx hy => rw [smul_add]; exact add_mem hx hy
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 := hmz z
    rw [hP, Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨a, ha⟩ := h1
    have h2 : ∑ k, a k • l (e k) = 0 := by
      have := congrArg θ ha
      rw [LinearMap.map_smul_of_tower, hz, smul_zero, map_sum] at this
      simpa [hθ] using this
    have h3 := Fintype.linearIndependent_iff.1 he a h2
    have h4 : m • z = 0 := by rw [← ha]; simp [h3]
    have h5 : Function.Injective ((m • LinearMap.id : M →ₗ[R] M).lTensor S) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ ((injective_iff_map_eq_zero _).2 hm)
    apply h5
    simpa using h4
  have e1 : (Submodule.span S (Set.range fun k => l (e k))).toAddSubgroup =
      (N.baseChange S).toAddSubgroup.map (θ : S ⊗[R] M →+ W) := by
    rw [← Submodule.map_toAddSubgroup, hP, Submodule.map_span, ← Set.range_comp]
    congr 3
    funext k; simp [hθ]
  have e2 : (Submodule.span S (Set.range l)).toAddSubgroup =
      (⊤ : AddSubgroup (S ⊗[R] M)).map (θ : S ⊗[R] M →+ W) := by
    rw [← Submodule.top_toAddSubgroup (R := S), ← Submodule.map_toAddSubgroup, Submodule.map_top, hθ,
      LinearMap.range_liftBaseChange]
    rfl
  rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective (f := (θ : S ⊗[R] M →+ W)) _ _ hinj, AddSubgroup.relIndex_top_right,
    Nat.card_congr (TensorProduct.tensorQuotientEquiv S N).toEquiv]
  rfl

open scoped ComplexOrder in

theorem det_le_of_dense {K ι κ : Type} [Field K] [Fintype ι] [Fintype κ] {j : ℕ} (σ : K →+* ℂ) (hσ : DenseRange σ)
    (A : Matrix ι (Fin j) ℂ) (B : Matrix κ (Fin j) ℂ) (t : ℝ)
    (h : ∀ x : Fin j → K, Formalism.HermitianLatticesTheory.cnorm (A *ᵥ fun k => σ (x k)) ≤ t * Formalism.HermitianLatticesTheory.cnorm (B *ᵥ fun k => σ (x k))) :
    (Aᴴ * A).det.re ≤ t ^ (2 * j) * (Bᴴ * B).det.re := by
  have hd : DenseRange (fun (x : Fin j → K) (k : Fin j) => σ (x k)) := DenseRange.piMap fun _ => hσ
  have h1 : ∀ y : Fin j → ℂ, Formalism.HermitianLatticesTheory.cnorm (A *ᵥ y) ≤ t * Formalism.HermitianLatticesTheory.cnorm (B *ᵥ y) := fun y => by
    refine hd.induction_on y (isClosed_le ?_ ?_) h
    · unfold Formalism.HermitianLatticesTheory.cnorm Matrix.mulVec dotProduct; fun_prop
    · unfold Formalism.HermitianLatticesTheory.cnorm Matrix.mulVec dotProduct; fun_prop
  have hq : ∀ {μ : Type} [Fintype μ] (C : Matrix μ (Fin j) ℂ) (y : Fin j → ℂ),
      star y ⬝ᵥ ((Cᴴ * C) *ᵥ y) = ((Formalism.HermitianLatticesTheory.cnorm (C *ᵥ y) ^ 2 : ℝ) : ℂ) := fun C y => by
    rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, Formalism.HermitianLatticesTheory.cnorm,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [dotProduct, Complex.conj_mul']
  have hA := Matrix.posSemidef_conjTranspose_mul_self A
  have hB := Matrix.posSemidef_conjTranspose_mul_self B
  have hY : (((t ^ 2 : ℝ) : ℂ) • (Bᴴ * B) - Aᴴ * A).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · refine IsHermitian.sub ?_ hA.isHermitian
      exact (hB.smul (Complex.zero_le_real.2 (sq_nonneg t))).isHermitian
    · rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, hq, hq, smul_eq_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_sub, Complex.zero_le_real, ← mul_pow, sub_nonneg]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (h1 y) 2
  have h2 := Formalism.DivisionValues.det_le_det_add hA hY
  rw [add_sub_cancel, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, ← pow_mul] at h2
  have h3 := (Complex.le_def.1 h2).1
  rwa [Complex.re_ofReal_mul] at h3

theorem denseRange_of_not_isReal {K : Type} [Field K] {σ : K →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · refine absurd (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)) hσ
    obtain ⟨r, hr⟩ := h.le (Subfield.le_topologicalClosure _ ⟨x, rfl⟩)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · rw [denseRange_iff_closure_range, ← RingHom.coe_fieldRange]
    exact congrArg (fun s : Subfield ℂ => (s : Set ℂ)) h

theorem sum_mk (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    ∑ σ : K →+* ℂ, g (InfinitePlace.mk σ) = 2 * ∑ v, g v := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : K →+* ℂ => InfinitePlace.mk σ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g v) (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
    Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq, (IsTotallyComplex.isComplex v).mult_eq_two]
  rfl

theorem sum_comap (K K' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K']
    [Algebra K K'] (g : InfinitePlace K → ℝ) :
    ∑ w : InfinitePlace K', g (w.comap (algebraMap K K')) = finrank K K' * ∑ v, g v := by
  classical
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  have h0 : ∀ τ : K →+* ℂ, Nat.card {σ : K' →+* ℂ // σ.comp (algebraMap K K') = τ} = finrank K K' := fun τ => by
    letI : Algebra K ℂ := τ.toAlgebra
    haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
    rw [← AlgHom.card K K' ℂ, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr ⟨fun σ => { σ.1 with commutes' := fun x => RingHom.congr_fun σ.2 x },
      fun φ => ⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩, fun σ => rfl, fun φ => rfl⟩
  have h1 : ∑ σ : K' →+* ℂ, g (InfinitePlace.mk (σ.comp (algebraMap K K'))) =
      (finrank K K' : ℝ) * ∑ σ : K →+* ℂ, g (InfinitePlace.mk σ) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : K' →+* ℂ => σ.comp (algebraMap K K')), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => g (InfinitePlace.mk τ))
      (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
      Finset.sum_const, nsmul_eq_mul, ← h0 τ, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 := sum_mk K' fun w => g (w.comap (algebraMap K K'))
  simp only [InfinitePlace.comap_mk] at h2
  rw [h1, sum_mk] at h2
  linarith

section Frames

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
  [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {j : ℕ}
  (e : Fin j → V)

def cols : Matrix ι (Fin j) ℂ := Matrix.of fun i a => Formalism.HermitianLatticesTheory.fcoord b X v (e a) i

theorem gramPl_eq : Formalism.HN.gramPl b X v e = (cols b X v e)ᴴ * cols b X v e := by
  ext a c
  simp [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, cols, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem normAt_sum (x : Fin j → K) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ k, x k • e k) = Formalism.HermitianLatticesTheory.cnorm (cols b X v e *ᵥ fun k => v.embedding (x k)) := by
  unfold Formalism.HermitianLatticesTheory.normAt
  congr 1
  funext i
  simp only [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, cols, Matrix.mulVec, dotProduct, map_sum, map_smul, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_mul, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Frames

theorem gram_le {K K' V V' ι κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [Field K']
    [NumberField K'] [StarRing K'] [Algebra K K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {b' : Basis κ K' V'} {X' : InfinitePlace K' → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K' →+* ℂ) → V' → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') {t : ℝ} (ht : ∀ σ' x, N' σ' (φ x) ≤ t * N (σ'.comp (algebraMap K K')) x)
    {j : ℕ} (e : Fin j → V) (w : InfinitePlace K') :
    (Formalism.HN.gramPl b' X' w fun k => φ (e k)).det.re ≤
      t ^ (2 * j) * (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re := by
  set σ := w.embedding.comp (algebraMap K K') with hσ
  have hv : w.comap (algebraMap K K') = InfinitePlace.mk σ := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  have hd : DenseRange σ := denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)
  have h1 : ∀ x : Fin j → K, Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => σ (x k)) ≤
      t * N σ (∑ k, x k • e k) := fun x => by
    have h := ht w.embedding (∑ k, x k • e k)
    rw [← (hG' w).2, map_sum] at h
    simp only [map_smulₛₗ] at h
    rw [normAt_sum] at h
    exact h
  rw [hv, gramPl_eq, gramPl_eq]
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · refine det_le_of_dense σ hd _ _ t fun x => (h1 x).trans (le_of_eq ?_)
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [this]
  · set B := cols b X (InfinitePlace.mk σ) e with hB
    have h2 : ((B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ)).det.re = (Bᴴ * B).det.re := by
      have : (B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (Bᴴ * B) := by
        ext a c
        simp [Matrix.mul_apply]
      rw [this, ← RingHom.map_det, Complex.conj_re]
    rw [← h2]
    refine det_le_of_dense σ hd _ _ t fun x => (h1 x).trans (le_of_eq ?_)
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [← hc]
    refine congrArg (t * ·) (this.trans ?_)
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.norm_conj]
    simp [Matrix.mulVec, dotProduct, hB]

theorem rk_mul_mu_eq {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) {j : ℕ} (e : Fin j → V)
    (he : LinearIndependent K e) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hle : Submodule.span (𝓞 K) (Set.range e) ≤ L) (hj : Formalism.HN.rkK L = j) :
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 ∧
      (∀ v, 0 < (Formalism.HN.gramPl b X v e).det.re) ∧
      (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X L) =
        Real.log ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) -
          ∑ v, Real.log (Formalism.HN.gramPl b X v e).det.re := by
  obtain ⟨h1, h2⟩ := Formalism.HN.htGram K V ι b X hX j e he
  have h3 := h2 L hL hle hj
  have p1 := (Formalism.HN.plLat K V ι b X hX L hL).2.2
  have p2 := (Formalism.HN.plLat K V ι b X hX _ (Submodule.fg_span (Set.finite_range e))).2.2
  have hi : ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := fun h => by
    rw [h, mul_zero] at h3
    exact p2.ne h3
  have hne : ∀ v ∈ Finset.univ, (Formalism.HN.gramPl b X v e).det.re ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (h1 ▸ p2.ne')
  refine ⟨by exact_mod_cast hi, fun v => lt_of_le_of_ne ?_ (hne v (Finset.mem_univ v)).symm, ?_⟩
  · rw [← Formalism.HN.HeightGram.norm_det_gramPl]; exact norm_nonneg _
  · have h4 := congrArg Real.log (h3.trans h1)
    rw [Real.log_mul p1.ne' hi, Real.log_prod hne] at h4
    have h5 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rk_mul_mu b X hX L hL
    rw [hj] at h5
    rw [h5, mul_div_cancel₀ _ Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero]
    linarith

theorem slope_sq_sub_le_slope_sq_span : ∀ (K K' V V' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (c : ℝ), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ' x, N' σ' (ι x) ≤ Real.exp c * N (σ'.comp (algebraMap K K')) x) → slope_sq N L - 2 * c ≤ slope_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) := by
  intro K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L c ⟨⟨n, ⟨b, X⟩, hG⟩⟩ ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ hc hli hL h0 hN
  letI : StarRing K := starRingOfComm
  letI : StarRing K' := starRingOfComm
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K V := Module.Finite.of_basis b
  letI : Module (𝓞 K) V' := Module.compHom V' (algebraMap (𝓞 K) (𝓞 K'))
  haveI : IsScalarTower (𝓞 K) (𝓞 K') V' := ⟨fun a s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let l : L →ₗ[𝓞 K] V' :=
    { toFun := fun x => ι x
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        show ι (a • (x : V)) = algebraMap (𝓞 K) (𝓞 K') a • ι x
        rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
        rfl }
  have hr : Set.range l = ι '' (L : Set V) := by
    ext y; simp [l]
  set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'
  have hL'fg : L'.FG := by
    haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 K) (M := L)
    refine ⟨(s.finite_toSet.image l).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, ← Submodule.span_span_of_tower (𝓞 K), ← Submodule.map_span, hs,
      Submodule.map_top, LinearMap.coe_range, hr]
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj0 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b L h0
  have hj : Formalism.HN.rkK L = finrank K (Submodule.span K (L : Set V)) := rfl
  rw [hj] at hj0
  generalize finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj hj0
  have he' := hli j e he
  have hj' : Formalism.HN.rkK L' = j := by
    have : Submodule.span K' (L' : Set V') = Submodule.span K' (Set.range fun k => ι (e k)) := by
      rw [hL', Submodule.span_span_of_tower]
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.subset_span hx)
        rw [map_sum]
        exact Submodule.sum_mem _ fun k _ => by
          rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩
    rw [Formalism.HN.rkK, this, finrank_span_eq_card he', Fintype.card_fin]
  obtain ⟨i1, g1, m1⟩ := rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  obtain ⟨-, g2, m2⟩ := rk_mul_mu_eq b' X' (fun v => (hG' v).1) _ he' L' hL'fg
    (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩)) hj'
  let eL : Fin j → L := fun k => ⟨e k, heL k⟩
  have hsub : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup := by
    have : Submodule.span (𝓞 K) (Set.range e) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    ext x
    rw [this]
    exact ⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have hidx : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := by
    rw [AddSubgroup.relIndex, hsub]; rfl
  rw [hidx] at i1 m1
  haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1
  have hidx' := relIndex_span (S := 𝓞 K') l eL (he'.restrict_scalars' (𝓞 K'))
    (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K)
    (fun x hx => by
      have h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : V) = 0 := by
        have := congrArg Subtype.val hx
        rw [Nat.cast_smul_eq_nsmul] at this ⊢
        exact this
      exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))
    (fun x => by
      rw [Nat.cast_smul_eq_nsmul]
      exact (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)
  rw [card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩), hr] at hidx'
  have m3 := m2
  rw [show (Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex L'.toAddSubgroup = _
    from hidx', Nat.cast_pow, Real.log_pow] at m3
  have hs : ∑ w, Real.log (Formalism.HN.gramPl b' X' w fun k => ι (e k)).det.re ≤
      ∑ w : InfinitePlace K', (2 * j * c + Real.log (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re) := by
    refine Finset.sum_le_sum fun w _ => (Real.log_le_log (g2 w) (gram_le hG hG' hc ι hN e w)).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (g1 _).ne', Real.log_pow, Real.log_exp]
    push_cast; ring
  rw [sum_comap K K' fun v => 2 * j * c + Real.log (Formalism.HN.gramPl b X v e).det.re, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hs
  have hf : (Formalism.HN.nPl K' : ℝ) = finrank K K' * Formalism.HN.nPl K := by
    simpa [Formalism.HN.nPl] using sum_comap K K' fun _ => 1
  have hf' : (0 : ℝ) < Formalism.HN.nPl K' := lt_of_le_of_ne (Nat.cast_nonneg _) Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero.symm
  have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
  rw [slope_sq_eq hG hL, slope_sq_eq hG' hL'fg]
  refine le_of_mul_le_mul_left (le_of_mul_le_mul_left ?_ hf') hjp
  have hc' : (Fintype.card (InfinitePlace K) : ℝ) = Formalism.HN.nPl K := rfl
  rw [hc'] at hs
  have m4 := congrArg ((finrank K K' : ℝ) * ·) m1
  rw [m3, hf]
  linarith

end GlobalTheory.SlopeExt
