import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

open IsDedekindDomain Formalism.L2.Host GroundTheory.Global GroundTheory.Global.IdeleGroup
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private noncomputable abbrev act (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n :=
  Matrix.GeneralLinearGroup.map (CT.adMap σ) g

private theorem ad_symm (σ : K ≃+* K) (a : 𝔸[K]) : CT.adMap σ.symm (CT.adMap σ a) = a := by
  rw [← (UpperTheory.ConvolutionTheory.K.adBasic K).2.2, RingEquiv.self_trans_symm, (UpperTheory.ConvolutionTheory.K.adBasic K).2.1]

private theorem act_symm (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n) : act σ.symm (act σ g) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => ad_symm σ _

private theorem act_mul (σ : K ≃+* K) (g h : AdelicGLn.AdelicGL K n) : act σ (g * h) = act σ g * act σ h :=
  map_mul (Matrix.GeneralLinearGroup.map (CT.adMap σ)) g h

private theorem act_unip (σ : K ≃+* K) {r : ℕ} (X : UPos n r → 𝔸[K]) :
    act σ (unipGL X) = unipGL fun p => CT.adMap σ (X p) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change CT.adMap σ (unipMatrix X i j) = unipMatrix _ i j
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem act_blk (σ : K ≃+* K) {a b : ℕ} (x : AdelicGLn.AdelicGL K a) (y : AdelicGLn.AdelicGL K b) :
    act σ (blk x y) = blk (act σ x) (act σ y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change CT.adMap σ (Matrix.fromBlocks x.val 0 0 y.val (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (act σ x).val 0 0 (act σ y).val (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with p | p <;> rcases finSumFinEquiv.symm j with q | q
  · rfl
  · exact map_zero _
  · exact map_zero _
  · rfl

open Classical in

private noncomputable def rl (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if hw : w.IsReal then ((ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm : ℂ ≃+* w.Completion).toRingHom.comp
    Complex.ofRealHom

omit [NumberField K] in
private theorem continuous_rl (w : InfinitePlace K) : Continuous (rl w) := by
  unfold rl
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      Complex.continuous_ofReal

private theorem pos_fst (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 w = rl w ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change posRealElem w (ρ ^ w.mult) = _
  unfold posRealElem rl
  split_ifs with hw
  · simp [InfinitePlace.mult, hw]
  · simp [InfinitePlace.mult, hw, Real.sqrt_sq hρ.le]

private theorem ad_pos (σ : K ≃+* K) (ρ : ℝ) (hρ : 0 < ρ) :
    CT.adMap σ ((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]) = ((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]) := by
  refine adele_ext (fun u => ?_) fun v => ?_
  · change CT.infEquiv σ u (((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 (u.comap σ.toRingHom)) = _
    rw [pos_fst, pos_fst]
    exact congrFun ((Rat.denseRange_cast (𝕜 := ℝ)).equalizer
      ((CT.continuous_infEquiv σ u).comp (continuous_rl (u.comap σ.toRingHom))) (continuous_rl u)
      (funext fun q => (map_ratCast ((CT.infEquiv σ u).toRingHom.comp (rl (u.comap σ.toRingHom))) q).trans
        (map_ratCast (rl u) q).symm)) ρ
  · change (CT.compEquiv σ.symm v).symm (((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).2 (CT.plMap σ.symm v)) = _
    rw [posIdele_finite, posIdele_finite, map_one]

private theorem act_central (σ : K ≃+* K) (s : {r : ℝ // 0 < r}) :
    act σ (centralSection K n s) = centralSection K n s := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change CT.adMap σ ((centralSection K n s : Matrix (Fin n) (Fin n) 𝔸[K]) i j) = _
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits, posIdeleHom_apply,
    Matrix.diagonal_apply]
  split_ifs
  · exact ad_pos σ _ _
  · exact map_zero _

private theorem norm_inf (σ : K ≃+* K) (u : InfinitePlace K) (y : (u.comap σ.toRingHom).Completion) :
    ‖CT.infEquiv σ u y‖ = ‖y‖ := by
  have hd : DenseRange (algebraMap K (u.comap σ.toRingHom).Completion) := by
    refine (((InfinitePlace.Completion.equiv (u.comap σ.toRingHom)).symm.surjective.denseRange).comp
      (UniformSpace.Completion.denseRange_coe (α := WithAbs (u.comap σ.toRingHom).1))
      (InfinitePlace.Completion.continuous_ofCompletion _)).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨x.ofAbs, rfl⟩
  have hn : ∀ (w : InfinitePlace K) (x : K), ‖algebraMap K w.Completion x‖ = w x := fun w x =>
    InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 x)
  refine congrFun (hd.equalizer (continuous_norm.comp (CT.continuous_infEquiv σ u)) continuous_norm
    (funext fun x => ?_)) y
  simp only [Function.comp_apply]
  rw [CT.infEquiv_algebraMap, hn, hn]
  rfl

private theorem mem_int (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) :
    y ∈ (ValuativeRel.valuation (v.adicCompletion K)).integer ↔ Valued.v y ≤ 1 := by
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one]

private theorem act_compact (σ : K ≃+* K) {k : AdelicGLn.AdelicGL K n} (hk : k ∈ (maxCompact : Subgroup _)) :
    act σ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) := by
  refine ⟨fun u y => ?_, fun v => ?_⟩
  · obtain ⟨x, rfl⟩ : ∃ x : Fin n → (u.comap σ.toRingHom).Completion, y = fun i => (CT.infEquiv σ u).toRingHom (x i) :=
      ⟨fun i => (CT.infEquiv σ u).symm (y i), funext fun i => ((CT.infEquiv σ u).apply_symm_apply _).symm⟩
    have hN := fun z : Fin n → (u.comap σ.toRingHom).Completion =>
      euclidNorm_map (CT.infEquiv σ u).toRingHom (norm_inf σ u) z
    have hv : Matrix.vecMul (fun i => (CT.infEquiv σ u).toRingHom (x i)) (infAt u (act σ k) : Matrix (Fin n) (Fin n) u.Completion) =
        fun j => (CT.infEquiv σ u).toRingHom
          (Matrix.vecMul x (infAt (u.comap σ.toRingHom) k : Matrix (Fin n) (Fin n) (u.comap σ.toRingHom).Completion) j) := by
      funext j
      simp only [Matrix.vecMul, dotProduct, map_sum, map_mul]
      rfl
    rw [hv, hN, hN, hk.1 (u.comap σ.toRingHom) x]
  · have h : ∀ y : (CT.plMap σ.symm v).adicCompletion K, y ∈ (ValuativeRel.valuation _).integer →
        (CT.compEquiv σ.symm v).symm y ∈ (ValuativeRel.valuation _).integer := fun y hy => by
      rw [mem_int] at hy ⊢
      rwa [← CT.valued_le_one_iff σ.symm v, RingEquiv.apply_symm_apply]
    have hv := (GLnLocal.mem_integralGL_iff _ _).1 (hk.2 (CT.plMap σ.symm v))
    have hf : finAt v (act σ k) =
        Matrix.GeneralLinearGroup.map (CT.compEquiv σ.symm v).symm.toRingHom (finAt (CT.plMap σ.symm v) k) := by
      ext i j
      rfl
    rw [hf]
    refine (GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => h _ (hv.1 i j), fun i j => ?_⟩
    rw [← map_inv]
    exact h _ (hv.2 i j)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.galLaws :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (σ : K ≃+* K) (θ : Twist μ) (θ₂ : Twist μ₂), UpperTheory.ConvolutionTheory.K.IsGal σ θ → UpperTheory.ConvolutionTheory.K.IsGal σ θ₂ →
      (∀ m₁ m₂ t, θ.e (lv m₁ m₂ t) = lv (θ₂.e m₁) (θ₂.e m₂) t) ∧ (∀ X, (∃ Y, θ.e (nn X) = nn Y) ∧ ∃ Y, θ.e.symm (nn X) = nn Y) ∧
      (∀ k, θ.e k ∈ KG K (2 + 2) ↔ k ∈ KG K (2 + 2)) ∧ (∀ γ, θ.e γ ∈ PK K ↔ γ ∈ PK K) ∧ ∀ g, HH (θ.e g) = HH g := by
  intro K _ _ μ _ μ₂ _ σ θ θ₂ h h₂
  have e : ∀ g, ((θ.e g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = act σ g := h
  have e₂ : ∀ g, ((θ₂.e g : G1 K 2) : AdelicGLn.AdelicGL K 2) = act σ g := h₂
  have hl : ∀ m₁ m₂ t, θ.e (lv m₁ m₂ t) = lv (θ₂.e m₁) (θ₂.e m₂) t := fun m₁ m₂ t => Subtype.ext (by
    rw [e, blkLaws.1, blkLaws.1, act_blk, act_mul, act_mul, e₂, e₂, zt, zt, act_central, act_central])
  have hn : ∀ X, θ.e (nn X) = nn fun p => Formalism.L2.Host.CT.adMap σ (X p) := fun X => Subtype.ext (by
    rw [e, coe_unipOne, coe_unipOne, act_unip])
  have hk : ∀ k, θ.e k ∈ KG K (2 + 2) ↔ k ∈ KG K (2 + 2) := fun k => by
    change ((θ.e k : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup _) ↔
      (k : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup _)
    rw [e]
    exact ⟨fun hh => act_symm σ (k : AdelicGLn.AdelicGL K (2 + 2)) ▸ act_compact σ.symm hh, act_compact σ⟩
  have hP : ∀ γ : G1 K (2 + 2), γ ∈ PK K ↔ γ ∈ Gam K (2 + 2) ∧ ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 →
      ((γ : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) i j = 0 := fun γ =>
    ⟨fun ⟨δ, hδ, hh⟩ => hh ▸ ⟨δ.2, (pkLaws.1 δ).1 hδ⟩, fun ⟨h1, h2⟩ => ⟨⟨γ, h1⟩, (pkLaws.1 ⟨γ, h1⟩).2 h2, rfl⟩⟩
  refine ⟨hl, fun X => ⟨⟨_, hn X⟩, fun p => Formalism.L2.Host.CT.adMap σ.symm (X p), ?_⟩, hk, fun γ => ?_, fun g => ?_⟩
  · apply θ.e.injective
    rw [θ.e.apply_symm_apply, hn]
    exact congrArg nn (funext fun p => (ad_symm σ.symm (X p)).symm)
  · rw [hP, hP, θ.mem_gam, e]
    refine and_congr_right fun _ => forall₄_congr fun i j _ _ => ?_
    change Formalism.L2.Host.CT.adMap σ (((γ : AdelicGLn.AdelicGL K (2 + 2)) : Matrix _ _ 𝔸[K]) i j) = 0 ↔ _
    exact map_eq_zero_iff _ (Function.LeftInverse.injective (ad_symm σ))
  · obtain ⟨X, m₁, m₂, t, k, hk', rfl⟩ := iwa g
    rw [map_mul, map_mul, hn, hl, hpSpec.1, hpSpec.1, (hpSpec.2.1 k hk').1, (hpSpec.2.1 _ ((hk k).2 hk')).1]
