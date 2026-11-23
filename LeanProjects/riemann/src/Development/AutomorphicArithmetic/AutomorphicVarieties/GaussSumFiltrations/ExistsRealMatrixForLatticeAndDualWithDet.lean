import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LatBasis

section Emb
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rhom_eq (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := by
  show InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x = (v.embedding x).re
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem coe_reAt (v : InfinitePlace F) (x : F) : ((reAt v x : ℝ) : ℂ) = v.embedding x := by
  rw [← rhom_eq]
  exact InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x

theorem emb_bij : Function.Bijective (fun v : InfinitePlace F => RingHom.equivRatAlgHom F ℂ v.embedding) := by
  refine (RingHom.equivRatAlgHom F ℂ).bijective.comp
    ⟨fun v w h => InfinitePlace.embedding_injective F h, fun φ => ?_⟩
  refine ⟨InfinitePlace.mk φ, ?_⟩
  have hr := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact h
  · rw [h] at hr ⊢
    exact ComplexEmbedding.isReal_iff.1 (ComplexEmbedding.isReal_conjugate_iff.1 hr)

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [coe_reAt]
  rw [show (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F x) by simp,
    trace_eq_sum_embeddings]
  exact Fintype.sum_bijective _ emb_bij _ _ (fun v => rfl)

theorem prod_reAt (x : F) : ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod]
  simp_rw [coe_reAt]
  rw [show (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) by simp,
    Algebra.norm_eq_prod_embeddings]
  exact Fintype.prod_bijective _ emb_bij _ _ (fun v => rfl)

theorem card_places : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [← AlgHom.card ℚ F ℂ]
  exact Fintype.card_congr (Equiv.ofBijective _ emb_bij)

theorem exists_basis [DecidableEq (InfinitePlace F)] : ∃ ω : Module.Basis (InfinitePlace F) ℚ F,
    (∀ x : F, IsIntegral ℤ x ↔ ∃ n : InfinitePlace F → ℤ, x = ∑ w, (n w : F) * ω w) ∧
    Algebra.discr ℚ ω = (discr F : ℚ) := by
  classical
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = Fintype.card (InfinitePlace F) := by
    rw [card_places, ← NumberField.RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e := Fintype.equivOfCardEq hc
  refine ⟨(NumberField.integralBasis F).reindex e, ?_, ?_⟩
  · intro x
    have h1 : IsIntegral ℤ x ↔
        x ∈ Submodule.span ℤ (Set.range ((NumberField.integralBasis F).reindex e)) := by
      rw [Module.Basis.range_reindex, NumberField.mem_span_integralBasis]
      constructor
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact NumberField.RingOfIntegers.isIntegral_coe y
    rw [h1, Submodule.mem_span_range_iff_exists_fun]
    simp only [zsmul_eq_mul]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  · rw [Module.Basis.coe_reindex, Algebra.discr_reindex, NumberField.coe_discr]

end Emb

theorem exists_root {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℝ) (h : G.PosDef) :
    ∃ R : Matrix κ κ ℝ, Rᵀ * R = G := by
  classical
  have hH := h.1
  refine ⟨Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * star (hH.eigenvectorUnitary : Matrix κ κ ℝ), ?_⟩
  conv_rhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  have hst : (star (hH.eigenvectorUnitary : Matrix κ κ ℝ))ᵀ = (hH.eigenvectorUnitary : Matrix κ κ ℝ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  rw [Matrix.transpose_mul, hst, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal, Matrix.mul_assoc]
  congr 3
  funext i
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
  exact Real.mul_self_sqrt (h.posSemidef.eigenvalues_nonneg i)

section Main
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {κ : Type} [Fintype κ] [DecidableEq κ]

noncomputable def em (v : InfinitePlace F) : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = em v x := (rhom_eq v x).symm

noncomputable def eM (R : Matrix κ κ ℝ) : (κ → F) →+ (InfinitePlace F × κ → ℝ) where
  toFun x p := ∑ j, R p.2 j * em p.1 (x j)
  map_zero' := by ext p; simp
  map_add' x y := by ext p; simp [mul_add, Finset.sum_add_distrib]

theorem eM_pair (G : Matrix κ κ ℤ) (R : Matrix κ κ ℝ) (hR : Rᵀ * R = G.map (Int.cast : ℤ → ℝ)) (x y : κ → F)
    (v : InfinitePlace F) : ∑ i, eM R x (v, i) * eM R y (v, i) = reAt v (BF G x y) := by
  rw [reAt_eq]
  have hG : ∀ i j, ((G i j : ℤ) : ℝ) = ∑ l, R l i * R l j := by
    intro i j
    have := congrFun (congrFun hR i) j
    simpa [Matrix.mul_apply] using this.symm
  simp only [eM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, BF, dotProduct, Matrix.mulVec, map_sum, map_mul,
    Matrix.map_apply, map_intCast, hG, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem eM_inj (R : Matrix κ κ ℝ) (hR : R.det ≠ 0) (x : κ → F) (h : eM R x = 0) : x = 0 := by
  have hv : ∀ v : InfinitePlace F, (fun i => em v (x i)) = 0 := by
    intro v
    apply Matrix.eq_zero_of_mulVec_eq_zero hR
    funext i
    have := congrFun h (v, i)
    simpa [eM, Matrix.mulVec, dotProduct] using this
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  funext j
  have := congrFun (hv v) j
  simpa using this

variable [DecidableEq (InfinitePlace F)]

noncomputable def aM (ω : Module.Basis (InfinitePlace F) ℚ F) (a : F) : Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
  Matrix.of fun v w => em v (a * ω w)

theorem det_aM_one (ω : Module.Basis (InfinitePlace F) ℚ F) : (aM ω 1).det ^ 2 = ((Algebra.discr ℚ ω : ℚ) : ℝ) := by
  classical
  let e : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) := Equiv.ofBijective _ emb_bij
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (⇑ω) e
  have hM : Algebra.embeddingsMatrixReindex ℚ ℂ (⇑ω) e = ((aM ω 1)ᵀ).map (fun r : ℝ => (r : ℂ)) := by
    ext i j
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm, Equiv.coe_refl, id,
      Equiv.symm_symm, Matrix.map_apply, Matrix.transpose_apply, aM, one_mul]
    rw [← reAt_eq, coe_reAt]
    rfl
  have hdet : (((aM ω 1)ᵀ).map (fun r : ℝ => (r : ℂ))).det = (((aM ω 1).det : ℝ) : ℂ) := by
    have h3 := RingHom.map_det Complex.ofRealHom (aM ω 1)ᵀ
    rw [Matrix.det_transpose] at h3
    exact h3.symm
  rw [hM, hdet] at h
  have h2 : (((Algebra.discr ℚ ω : ℚ) : ℝ) : ℂ) = (((aM ω 1).det ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, ← h]
    simp
  exact (Complex.ofReal_injective h2).symm

theorem det_aM (ω : Module.Basis (InfinitePlace F) ℚ F) (a : F) :
    (aM ω a).det = ((Algebra.norm ℚ a : ℚ) : ℝ) * (aM ω 1).det := by
  have h : aM ω a = Matrix.diagonal (fun v => em v a) * aM ω 1 := by
    ext v w
    simp [aM, Matrix.diagonal_mul, map_mul]
  rw [h, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  rw [← prod_reAt]
  exact Finset.prod_congr rfl (fun v _ => (reAt_eq v a).symm)

noncomputable def bM (ω : Module.Basis (InfinitePlace F) ℚ F) (a : F) (R : Matrix κ κ ℝ) :
    Matrix (InfinitePlace F × κ) (InfinitePlace F × κ) ℝ := Matrix.kroneckerMap (fun x y => x * y) (aM ω a) R

theorem bM_mulVec (ω : Module.Basis (InfinitePlace F) ℚ F) (a : F) (R : Matrix κ κ ℝ) (m : InfinitePlace F × κ → ℤ) :
    eM R (a • fun j => ∑ w, (m (w, j) : F) * ω w) = bM ω a R *ᵥ fun i => (m i : ℝ) := by
  funext p
  simp only [eM, bM, aM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_sum,
    map_intCast, Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
  ring

theorem bM_transpose (G : Matrix κ κ ℤ) (R : Matrix κ κ ℝ) (hR : Rᵀ * R = G.map (Int.cast : ℤ → ℝ))
    (ω : Module.Basis (InfinitePlace F) ℚ F) (a : F) (y : κ → F) (q : InfinitePlace F × κ) :
    ((bM ω a R)ᵀ *ᵥ eM R y) q = ((Algebra.trace ℚ F (BF G (a • y) (Pi.single q.2 (ω q.1))) : ℚ) : ℝ) := by
  have hG : ∀ i j, ((G i j : ℤ) : ℝ) = ∑ l, R l i * R l j := by
    intro i j
    have := congrFun (congrFun hR i) j
    simpa [Matrix.mul_apply] using this.symm
  have hsym : ∀ i j, ((G i j : ℤ) : ℝ) = ((G j i : ℤ) : ℝ) := by
    intro i j
    rw [hG, hG]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hB : BF G (a • y) (Pi.single q.2 (ω q.1)) = ∑ i, a * y i * ((G i q.2 : ℤ) : F) * ω q.1 := by
    simp only [BF, dotProduct, Matrix.mulVec, Pi.single_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hB, ← sum_reAt]
  simp only [reAt_eq, map_sum, map_mul, map_intCast, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    bM, aM, eM, Matrix.kroneckerMap_apply, Matrix.of_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp_rw [hsym _ q.2, hG, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem mem_LL (x : κ → F) : x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]

theorem exists_alpha (ω : Module.Basis (InfinitePlace F) ℚ F)
    (hω : ∀ x : F, IsIntegral ℤ x ↔ ∃ n : InfinitePlace F → ℤ, x = ∑ w, (n w : F) * ω w) (a : F) (ha : a ≠ 0) :
    ∃ α : (InfinitePlace F × κ → ℤ) ≃ aL κ a, ∀ m, (α m : κ → F) = a • fun j => ∑ w, (m (w, j) : F) * ω w := by
  classical
  let g : (InfinitePlace F × κ → ℤ) → (κ → F) := fun m => a • fun j => ∑ w, (m (w, j) : F) * ω w
  have hmem : ∀ m, g m ∈ aL κ a := by
    intro m
    refine AddSubgroup.mem_map.2 ⟨fun j => ∑ w, (m (w, j) : F) * ω w, ?_, rfl⟩
    rw [mem_LL]
    intro j
    exact (hω _).2 ⟨fun w => m (w, j), rfl⟩
  have hinj : Function.Injective (fun m => (⟨g m, hmem m⟩ : aL κ a)) := by
    intro m m' h
    have h' : g m = g m' := congrArg Subtype.val h
    funext p
    obtain ⟨w, j⟩ := p
    have hj := congrFun h' j
    simp only [g, Pi.smul_apply, smul_eq_mul] at hj
    have hj2 := mul_left_cancel₀ ha hj
    have hli := ω.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun w => ((m (w, j) : ℚ) - m' (w, j))) (by
      simp only [Algebra.smul_def, map_sub, map_intCast, sub_mul, Finset.sum_sub_distrib, hj2, sub_self])
    exact_mod_cast sub_eq_zero.1 (this w)
  have hsurj : ∀ y : aL κ a, ∃ m, g m = y := by
    rintro ⟨y, hy⟩
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hy
    rw [mem_LL] at hl
    choose n hn using fun j => (hω (l j)).1 (hl j)
    refine ⟨fun p => n p.2 p.1, ?_⟩
    funext j
    simp only [g, Pi.smul_apply, smul_eq_mul, DistribMulAction.toAddMonoidHom_apply]
    rw [hn j]
  refine ⟨Equiv.ofBijective _ ⟨hinj, fun y => ?_⟩, fun m => rfl⟩
  obtain ⟨m, hm⟩ := hsurj y
  exact ⟨m, Subtype.ext hm⟩

theorem mem_dualL (G : Matrix κ κ ℤ) (ω : Module.Basis (InfinitePlace F) ℚ F)
    (hω : ∀ x : F, IsIntegral ℤ x ↔ ∃ n : InfinitePlace F → ℤ, x = ∑ w, (n w : F) * ω w) (y : κ → F) :
    y ∈ dualL F G ↔ ∀ q : InfinitePlace F × κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y (Pi.single q.2 (ω q.1))) = n := by
  classical
  show (∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n) ↔ _
  constructor
  · intro hy q
    apply hy
    rw [mem_LL]
    intro j
    by_cases hj : j = q.2
    · subst hj
      rw [Pi.single_eq_same]
      exact (hω _).2 ⟨Pi.single q.1 1, by simp [Pi.single_apply]⟩
    · rw [Pi.single_eq_of_ne hj]
      exact isIntegral_zero
  · intro h l hl
    rw [mem_LL] at hl
    choose n hn using fun j => (hω (l j)).1 (hl j)
    choose N hN using h
    refine ⟨∑ k, ∑ w, n k w * N (w, k), ?_⟩
    have hBF : ∀ z : κ → F, BF G y z = ∑ k, (y ᵥ* G.map (Int.cast : ℤ → F)) k * z k := by
      intro z
      simp only [BF]
      rw [Matrix.dotProduct_mulVec]
      rfl
    have hsingle : ∀ k w, BF G y (Pi.single k (ω w)) = (y ᵥ* G.map (Int.cast : ℤ → F)) k * ω w := by
      intro k w
      simp only [BF]
      rw [Matrix.dotProduct_mulVec, dotProduct_single]
    have hl' : BF G y l = ∑ k, ∑ w, (n k w : F) * BF G y (Pi.single k (ω w)) := by
      rw [hBF]
      simp only [hsingle]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hn k, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have htr : ∀ (c : ℤ) (z : F), Algebra.trace ℚ F ((c : F) * z) = c * Algebra.trace ℚ F z := by
      intro c z
      rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
    rw [hl', map_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [htr, hN (w, k)]

noncomputable def pairL (G : Matrix κ κ ℤ) (ω : Module.Basis (InfinitePlace F) ℚ F) (a : F) :
    (κ → F) →ₗ[ℚ] (InfinitePlace F × κ → ℚ) where
  toFun y q := Algebra.trace ℚ F (BF G (a • y) (Pi.single q.2 (ω q.1)))
  map_add' x y := by
    funext q
    simp only [BF, smul_add, add_dotProduct, map_add, Pi.add_apply]
  map_smul' c x := by
    funext q
    simp only [BF, smul_comm a c, smul_dotProduct, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem exists_beta (G : Matrix κ κ ℤ) (R : Matrix κ κ ℝ) (hR : Rᵀ * R = G.map (Int.cast : ℤ → ℝ)) (hd : R.det ≠ 0)
    (ω : Module.Basis (InfinitePlace F) ℚ F)
    (hω : ∀ x : F, IsIntegral ℤ x ↔ ∃ n : InfinitePlace F → ℤ, x = ∑ w, (n w : F) * ω w) (a : F)
    (hB : (bM ω a R).det ≠ 0) :
    ∃ β : (InfinitePlace F × κ → ℤ) ≃ {y : κ → F // a • y ∈ dualL F G},
      ∀ m, eM R (β m) = (bM ω a R)⁻¹ᵀ *ᵥ fun i => (m i : ℝ) := by
  classical
  set B := bM ω a R with hBdef
  let P := pairL G ω a
  have hP : ∀ y q, (Bᵀ *ᵥ eM R y) q = ((P y q : ℚ) : ℝ) := fun y q => bM_transpose G R hR ω a y q
  have hBt : IsUnit Bᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 hB
  have hinj : Function.Injective P := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply eM_inj R hd y
    have h0 : Bᵀ *ᵥ eM R y = 0 := by
      funext q
      rw [hP, hy]
      simp
    have h1 := congrArg (fun v => Bᵀ⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hBt] using h1
  have hrank : Module.finrank ℚ (κ → F) = Module.finrank ℚ (InfinitePlace F × κ → ℚ) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
      card_places, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hsurj : Function.Surjective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  let Pe := LinearEquiv.ofBijective P ⟨hinj, hsurj⟩
  have hPe : ∀ y, Pe y = P y := fun y => rfl
  have hmem : ∀ y, a • y ∈ dualL F G ↔ ∀ q, ∃ n : ℤ, P y q = n := fun y => mem_dualL G ω hω (a • y)
  have hPs : ∀ (m : InfinitePlace F × κ → ℤ) q, P (Pe.symm (fun q => (m q : ℚ))) q = m q := by
    intro m q
    rw [← hPe, LinearEquiv.apply_symm_apply]
  refine ⟨{ toFun := fun m => ⟨Pe.symm (fun q => (m q : ℚ)), (hmem _).2 fun q => ⟨m q, hPs m q⟩⟩
            invFun := fun y q => Classical.choose ((hmem y.1).1 y.2 q)
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro m
    funext q
    dsimp only
    have h := Classical.choose_spec ((hmem (Pe.symm (fun q => (m q : ℚ)))).1
      ((hmem _).2 fun q => ⟨m q, hPs m q⟩) q)
    have h2 := h.symm.trans (hPs m q)
    exact_mod_cast h2
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    dsimp only
    apply Pe.injective
    rw [LinearEquiv.apply_symm_apply]
    funext q
    rw [hPe]
    exact (Classical.choose_spec ((hmem y).1 hy q)).symm
  · intro m
    dsimp only [Equiv.coe_fn_mk]
    have h1 : Bᵀ *ᵥ eM R (Pe.symm (fun q => (m q : ℚ))) = fun i => (m i : ℝ) := by
      funext q
      rw [hP, hPs]
      push_cast
      rfl
    rw [Matrix.transpose_nonsing_inv, ← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hBt,
      Matrix.one_mulVec]

end Main

theorem lattice_matrix : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [DecidableEq (InfinitePlace F)] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ a : F, a ≠ 0 → ∃ (e : (κ → F) →+ (InfinitePlace F × κ → ℝ)) (B : Matrix (InfinitePlace F × κ) (InfinitePlace F × κ) ℝ) (α : (InfinitePlace F × κ → ℤ) ≃ aL κ a) (β : (InfinitePlace F × κ → ℤ) ≃ {y : κ → F // a • y ∈ dualL F G}), (∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) ∧ (∀ m, e (α m) = B *ᵥ fun i => (m i : ℝ)) ∧ (∀ m, e (β m) = B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ∧ B.det ≠ 0 ∧ |B.det| = ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (2 * k) * ((discr F).natAbs : ℝ) ^ k * (t : ℝ) ^ Module.finrank ℚ F := by
  intro F _ _ _ _ κ _ _ G hG t ht k hk a ha
  obtain ⟨ω, hω, hdisc⟩ := exists_basis (F := F)
  obtain ⟨R, hR⟩ := exists_root (G.map (Int.cast : ℤ → ℝ)) hG.1
  have hG' : (G.map (Int.cast : ℤ → ℝ)).det = ((G.det : ℤ) : ℝ) := by
    exact (RingHom.map_det (Int.castRingHom ℝ) G).symm
  have hdetR : R.det ^ 2 = (t : ℝ) ^ 2 := by
    have h1 := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_transpose] at h1
    rw [sq, h1, hG', ht]
    push_cast
    ring
  have hRpos : 0 < R.det * R.det := by
    have h2 := hG.1.det_pos
    rw [← hR, Matrix.det_mul, Matrix.det_transpose] at h2
    exact h2
  have hRd : R.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hRpos
    exact lt_irrefl _ hRpos
  have hRabs : |R.det| = (t : ℝ) := by
    rw [(sq_eq_sq_iff_abs_eq_abs _ _).1 hdetR, abs_of_nonneg (Nat.cast_nonneg t)]
  have hA1 : (aM ω 1).det ^ 2 = ((discr F : ℤ) : ℝ) := by
    rw [det_aM_one, hdisc, Rat.cast_intCast]
  have hA1ne : (aM ω 1).det ≠ 0 := by
    intro h
    rw [h] at hA1
    have h3 := NumberField.discr_ne_zero F
    apply h3
    exact_mod_cast (by simpa using hA1.symm : ((discr F : ℤ) : ℝ) = 0)
  have hNa : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hdetB : (bM ω a R).det
      = (aM ω a).det ^ Fintype.card κ * R.det ^ Fintype.card (InfinitePlace F) := by
    unfold bM
    exact Matrix.det_kronecker (aM ω a) R
  have hB : (bM ω a R).det ≠ 0 := by
    rw [hdetB, det_aM]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hA1ne)) (pow_ne_zero _ hRd)
    exact_mod_cast hNa
  obtain ⟨α, hα⟩ := exists_alpha (κ := κ) ω hω a ha
  obtain ⟨β, hβ⟩ := exists_beta G R hR hRd ω hω a hB
  refine ⟨eM R, bM ω a R, α, β, fun x y v => eM_pair G R hR x y v, fun m => ?_, hβ, hB, ?_⟩
  · rw [hα m]
    exact bM_mulVec ω a R m
  · have hdn : (0 : ℝ) ≤ ((discr F : ℤ) : ℝ) := by
      rw [← hA1]
      positivity
    rw [hdetB, det_aM, abs_mul, abs_pow, abs_pow, hRabs, card_places, hk, abs_mul,
      mul_pow, pow_mul (|(aM ω 1).det|), sq_abs, hA1, Nat.cast_natAbs, Int.cast_abs,
      abs_of_nonneg hdn]
    rw [pow_mul, pow_mul, sq_abs]

end GlobalTheory.HilbertThetaSeries.LatBasis

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realMatrix_for_lattice_and_dual_with_det : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [DecidableEq (InfinitePlace F)] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ a : F, a ≠ 0 → ∃ (e : (κ → F) →+ (InfinitePlace F × κ → ℝ)) (B : Matrix (InfinitePlace F × κ) (InfinitePlace F × κ) ℝ) (α : (InfinitePlace F × κ → ℤ) ≃ aL κ a) (β : (InfinitePlace F × κ → ℤ) ≃ {y : κ → F // a • y ∈ dualL F G}), (∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) ∧ (∀ m, e (α m) = B *ᵥ fun i => (m i : ℝ)) ∧ (∀ m, e (β m) = B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ∧ B.det ≠ 0 ∧ |B.det| = ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (2 * k) * ((discr F).natAbs : ℝ) ^ k * (t : ℝ) ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.HilbertThetaSeries.LatBasis.lattice_matrix | exact GlobalTheory.HilbertThetaSeries.LatBasis.lattice_matrix | (intros; apply GlobalTheory.HilbertThetaSeries.LatBasis.lattice_matrix <;> assumption)
