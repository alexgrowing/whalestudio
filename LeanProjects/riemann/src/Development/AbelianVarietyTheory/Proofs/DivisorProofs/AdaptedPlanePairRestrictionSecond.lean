import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictsToAdaptedXStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXDblChar

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

theorem exists_cont_char : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∀ (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)) (omd₁ : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ)),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → IsUSplitting (adeleClass F) B.ψ dd₁ (actB (cA σ)) omd₁ →
      ∀ ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l ∘ₗ ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ≠ 0) →
      ∃ cd : UG (cA σ) (dbl (incM F W.J)) →* ℂˣ, Continuous cd ∧
        ∀ g, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (omd g Φ) = (cd g : ℂ) • omd₁ g (ed Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁
    omd omd₁ hS hS₁ ed hmap hheis hinv hadm hnz
  obtain ⟨Φ₀, hΦ₀, hΦ₀0⟩ := id hnz
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hΦ₀0
  simp only [Pi.zero_apply] at hx
  have inv_mul : ∀ p φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have inv_mul₁ : ∀ p φ, omd₁ p (omd₁ p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsp : ∀ p, ∀ φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), omd p φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    fun p φ hφ => hS.pres p φ hφ
  have key : ∀ p, ∃ k : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (omd p Φ) = k • omd₁ p (ed Φ) :=
    fun p => by
    obtain ⟨k, hk⟩ := GlobalTheory.T.pair_restricts_to_adapted_x hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne
      dd dd₁ hdd hdd₁ ed hmap hheis hinv hadm hnz (omd₁ p⁻¹ ∘ₗ ed ∘ₗ omd p)
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
  have huniq : ∀ p (k : ℂ), (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (omd p Φ) = k • omd₁ p (ed Φ)) →
      k = cf p := fun p k hk => by
    have h1 := hk _ (hsp p⁻¹ _ hΦ₀)
    have h2 := hcf p _ (hsp p⁻¹ _ hΦ₀)
    rw [inv_mul] at h1 h2
    have h3 := congrFun (h1.symm.trans h2) x
    have h4 := congrFun h1 x
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    have hV : omd₁ p (ed (omd p⁻¹ Φ₀)) x ≠ 0 := fun h0 => hx (by rw [h4, h0, mul_zero])
    exact mul_right_cancel₀ hV h3
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun Φ hΦ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf p _ (hsp q Φ hΦ), hcf q Φ hΦ, map_smul,
      smul_smul]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun Φ _ => by simp).symm
  have hne0 : ∀ p, cf p ≠ 0 := fun p h => by
    have := hmul p p⁻¹
    rw [mul_inv_cancel, hone, h, zero_mul] at this
    exact one_ne_zero this
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ _ hΦ₀
    have hf := hS.cont _ (hadm _ (evAt_mem_adm _ x)) _ hφ
    have hg := hS₁.cont _ (evAt_mem_adm _ x) _ (hmap _ hφ)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hf hg
    have h0 : omd₁ p₀ (ed (omd p₀⁻¹ Φ₀)) x ≠ 0 := by
      rw [hcf p₀⁻¹ _ hΦ₀, map_smul, inv_mul₁]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (hne0 _) hx
    refine (hf.continuousAt.div hg.continuousAt h0).congr ?_
    filter_upwards [hg.continuousAt.eventually_ne h0] with p hp
    have := congrFun (hcf p _ hφ) x
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.div_apply]
    rw [this, mul_div_cancel_right₀ _ hp]
  let cM : UG (cA σ) (dbl (incM F W.J)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let cU := cM.toHomUnits
  have hcv : ∀ p, ((cU p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcontU : Continuous cU := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((cU p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ hne0
  exact ⟨cU, hcontU, fun g Φ hΦ => by rw [hcv]; exact hcf g Φ hΦ⟩

end GlobalTheory.MixXDblChar
end
