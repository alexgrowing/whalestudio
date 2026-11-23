import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionGlobalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionArchimedeanStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixWOne

open scoped Classical in

theorem evAt_mem_adm {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (x₀ : κ → AF F) :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) x₀) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x₀ i).2) • (BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hrs.symm).trans finSumFinEquiv.symm
  have key : (A.submatrix id e)ᵀ * M * (A.submatrix id e).map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e e := by
    rw [← hA]; ext i j; simp [Matrix.mul_apply, Matrix.submatrix_apply]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact absurd this.symm (pow_ne_zero _ (by norm_num))

theorem actB_mul_left {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α α' β : Type}
    [Fintype β] [DecidableEq β] [Fintype α'] {J : Matrix β β E'} (p : UG c J) (A : Matrix α α' E') (x : Matrix α' β E') :
    actB c p (A * x) = A * actB c p x := by
  unfold actB; rw [Matrix.mul_assoc]

theorem actB_vecMulVec {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α β : Type}
    [Fintype β] [DecidableEq β] {J : Matrix β β E'} (p : UG c J) (u : α → E') (y : β → E') :
    actB c p (Matrix.vecMulVec u y) = Matrix.vecMulVec u (y ᵥ* ((p : GL β E') : Matrix β β E')ᵀ) := by
  unfold actB; exact Matrix.vecMulVec_mul _ _ _

theorem actB_inv_actB {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α β : Type}
    [Fintype β] [DecidableEq β] {J : Matrix β β E'} (p : UG c J) (x : Matrix α β E') :
    actB c p⁻¹ (actB c p x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have : ((↑(p⁻¹) : GL β E') : Matrix β β E') * ((p : GL β E') : Matrix β β E') = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  rw [this, Matrix.transpose_one, Matrix.mul_one]

theorem evalZero_scalar_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ c : UA σ X.J →* ℂˣ, (∀ g, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = (c g : ℂ) • om₁ (g, 1) (e Φ)) → c = 1 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he c hc
  obtain ⟨-, ⟨d', hd', hA⟩, -⟩ := hP.weil
  obtain ⟨-, dd, omd, hdd, hWS, hres⟩ := hA
  obtain ⟨-, hS, -⟩ := id hWS
  obtain ⟨-, ⟨d₁', hd₁', hA₁⟩, -⟩ := hP₁.weil
  obtain ⟨-, dd₁, omd₁, hdd₁, hWS₁, hres₁⟩ := hA₁
  obtain ⟨-, hS₁, -⟩ := id hWS₁
  obtain ⟨ed, hmap, hheis, hinv, hadm, Φ₂, hΦ₂, Ψ₂, hΨ₂, hΨ₂0, hbox⟩ :=
    GlobalTheory.T.seesaw_pair_restriction_local_factor hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
      dd₁ hdd₁ e he
  obtain ⟨Φ₁, hΦ₁, hΦ₁0⟩ := GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  have hb0 : boxFun Φ₁ Φ₂ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F _ _ Φ₁ hΦ₁ Φ₂ hΦ₂
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hΦ₁0
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hΨ₂0
  simp only [Pi.zero_apply] at ha hb
  have hx₀0 : ed (boxFun Φ₁ Φ₂) (Sum.elim a b) ≠ 0 := by
    rw [hbox Φ₁ hΦ₁]
    simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    exact mul_ne_zero ha hb
  have hnz : ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ≠ 0 :=
    ⟨boxFun Φ₁ Φ₂, hb0, fun h => hx₀0 (by rw [h]; rfl)⟩
  have inv_mul : ∀ p φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have inv_mul₁ : ∀ p φ, omd₁ p (omd₁ p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsp : ∀ p, ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), omd p φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    fun p φ hφ => hS.pres p φ hφ
  have key : ∀ p, ∃ k : ℂ, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed (omd p Φ) = k • omd₁ p (ed Φ) :=
    fun p => by
    obtain ⟨k, hk⟩ := GlobalTheory.T.seesaw_pair_restriction_global_factor hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁'
      hd₁' dd hdd dd₁ hdd₁ ed hmap hheis hinv hadm hnz (omd₁ p⁻¹ ∘ₗ ed ∘ₗ omd p)
      (fun Φ hΦ => hS₁.pres _ _ (hmap _ (hS.pres _ _ hΦ)))
      (fun z Φ hΦ => by
        simp only [LinearMap.comp_apply]
        rw [hS.impl p _ Φ hΦ, actB_mul_left, hheis _ _ (hS.pres _ _ hΦ),
          hS₁.impl _ _ _ (hmap _ (hS.pres _ _ hΦ)), actB_inv_actB])
      (fun y Φ hΦ => by
        simp only [LinearMap.comp_apply]
        rw [hS.impl p _ Φ hΦ, actB_vecMulVec, hinv _ _ (hS.pres _ _ hΦ)])
      (fun l hl => by
        have e0 : l ∘ₗ (omd₁ p⁻¹ ∘ₗ ed ∘ₗ omd p) = ((l ∘ₗ omd₁ p⁻¹) ∘ₗ ed) ∘ₗ omd p := rfl
        rw [e0]
        exact hS.adm p _ (hadm _ (hS₁.adm p⁻¹ l hl)))
    refine ⟨k, fun Φ hΦ => ?_⟩
    have := congrArg (omd₁ p) (hk Φ hΦ)
    simpa [LinearMap.comp_apply, inv_mul₁, map_smul] using this
  choose cf hcf using key
  have huniq : ∀ p (k : ℂ), (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed (omd p Φ) = k • omd₁ p (ed Φ)) →
      k = cf p := fun p k hk => by
    have h1 := hk _ (hsp p⁻¹ _ hb0)
    have h2 := hcf p _ (hsp p⁻¹ _ hb0)
    rw [inv_mul] at h1 h2
    have h3 := congrFun (h1.symm.trans h2) (Sum.elim a b)
    have h4 := congrFun h1 (Sum.elim a b)
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    have hV : omd₁ p (ed (omd p⁻¹ (boxFun Φ₁ Φ₂))) (Sum.elim a b) ≠ 0 := fun h0 => hx₀0 (by rw [h4, h0, mul_zero])
    exact mul_right_cancel₀ hV h3
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun Φ hΦ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf p _ (hsp q Φ hΦ), hcf q Φ hΦ, map_smul,
      smul_smul]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun Φ _ => by simp).symm
  have hne : ∀ p, cf p ≠ 0 := fun p h => by
    have := hmul p p⁻¹
    rw [mul_inv_cancel, hone, h, zero_mul] at this
    exact one_ne_zero this
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ _ hb0
    have hf := hS.cont _ (hadm _ (evAt_mem_adm _ (Sum.elim a b))) _ hφ
    have hg := hS₁.cont _ (evAt_mem_adm _ (Sum.elim a b)) _ (hmap _ hφ)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hf hg
    have h0 : omd₁ p₀ (ed (omd p₀⁻¹ (boxFun Φ₁ Φ₂))) (Sum.elim a b) ≠ 0 := by
      rw [hcf p₀⁻¹ _ hb0, map_smul, inv_mul₁]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (hne _) hx₀0
    refine (hf.continuousAt.div hg.continuousAt h0).congr ?_
    filter_upwards [hg.continuousAt.eventually_ne h0] with p hp
    have := congrFun (hcf p _ hφ) (Sum.elim a b)
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.div_apply]
    rw [this, mul_div_cancel_right₀ _ hp]
  let cM : UG (cA σ) (dbl (incM F X.J)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let cU := cM.toHomUnits
  have hcv : ∀ p, ((cU p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcontU : Continuous cU := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((cU p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ hne
  have hP3 := GlobalTheory.T.seesaw_pair_restriction_archimedean hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd
    hdd dd₁ hdd₁ omd hWS omd₁ hWS₁ ed hmap hheis hinv hadm hnz cf hcf
  have hσ : IsCMExt F E σ := hP.base.cm
  have hJ : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hP.herm.herm i j]
  have hdet : X.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    intro h0
    apply det_ne_zero_of_hasSig (hP.herm.sig w)
    have := RingHom.map_det (B.emb w).1 X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ n X.J 1 hJ hdet cU hcontU (fun p t hpt => Units.ext (by
    rw [hcv, Units.val_one]; exact hP3 p t hpt))
  refine MonoidHom.ext fun g => Units.ext ?_
  rw [MonoidHom.one_apply, Units.val_one]
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin n) (incM F X.J) g
  have hcd : cf gd = 1 := by rw [← hcv, hc1]; rfl
  have hpres : om (g, 1) Φ₁ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres (g, 1) Φ₁ hΦ₁
  have e1 := hres g gd hgd Φ₁ hΦ₁ Φ₂ hΦ₂
  have e2 := hres₁ g gd hgd (e Φ₁) (he.maps Φ₁ hΦ₁) Ψ₂ hΨ₂
  have e3 := hcf gd _ hb0
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at e1 e2
  rw [e1, hbox _ hpres, hbox Φ₁ hΦ₁, e2, hcd, one_smul, hc g Φ₁ hΦ₁] at e3
  have hV : om₁ (g, 1) (e Φ₁) ≠ 0 := fun h0 => hΦ₁0 (by
    have := congrArg (om₁ (g⁻¹, 1)) h0
    rwa [← Module.End.mul_apply, ← map_mul, map_zero, show ((g⁻¹, 1) : UA σ X.J × UA σ W₁.J) * (g, 1) = 1 by simp,
      map_one, Module.End.one_apply] at this)
  obtain ⟨a', ha'⟩ := Function.ne_iff.mp hV
  simp only [Pi.zero_apply] at ha'
  have e4 := congrFun e3 (Sum.elim a' b)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.smul_apply, smul_eq_mul] at e4
  exact mul_right_cancel₀ (mul_ne_zero ha' hb) (by rw [one_mul, ← mul_assoc]; exact e4)
end GlobalTheory.MixWOne
end
