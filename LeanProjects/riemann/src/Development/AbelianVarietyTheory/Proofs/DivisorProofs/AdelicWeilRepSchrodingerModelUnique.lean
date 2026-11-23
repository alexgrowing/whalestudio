import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilSchUnique

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem scalar_of_commute (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (ha : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (hc : ∀ w, ∀ φ ∈ schA F κ, T (schr ψ w φ) = schr ψ w (T φ)) :
    ∃ c : ℂ, ∀ φ ∈ schA F κ, T φ = c • φ := by
  obtain ⟨c, hc'⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ (LinearMap.proj 0 ∘ₗ T) (ha _ (evalZero_mem_adelicSchwartzAdmittedForms κ)) (fun y φ hφ => by
    have e : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [e, hc _ φ hφ]; simp [schr])
  refine ⟨c, fun φ hφ => funext fun x => ?_⟩
  have h1 := congrFun (hc (x, 0) φ hφ) 0
  have e : schr ψ (x, 0) φ = fun z => φ (z + x) := by funext z; simp [schr]
  have h2 := hc' _ (e ▸ GlobalTheory.T.adelicSchwartzSpace_translate_mem F κ x φ hφ)
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at h2
  rw [h1] at h2
  simp [schr] at h2
  simpa [e] using h2

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem actB_inv_actB {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α β : Type}
    [Fintype β] [DecidableEq β] {J : Matrix β β E'} (p : UG c J) (x : Matrix α β E') :
    actB c p⁻¹ (actB c p x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have : ((↑(p⁻¹) : GL β E') : Matrix β β E') * ((p : GL β E') : Matrix β β E') = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  rw [this, Matrix.transpose_one, Matrix.mul_one]

theorem dd_rho_diag {a b : ℕ} {σ : E →ₐ[F] E} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    {dd : Darboux (symp (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)}
    (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (AE F E)) :
    dd.rho ψ (z * (diagCols (Fin b))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

theorem member_unique (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ) (χ : Chr F E)
    (om om₁ : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (h₁ : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om₁) :
    ∀ g, ∀ Φ ∈ schA F κ, om g Φ = om₁ g Φ := by
  obtain ⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  have hee : ∀ w, dd₁.e w = dd.e w := fun w => by
    rw [← Matrix.fromCols_toCols w, hdd, hdd₁]
  have hrho : ∀ w, dd₁.rho ψ w = dd.rho ψ w := fun w => by simp only [Darboux.rho, hee]
  have inv_mul : ∀ (p : UG (cA σ) (dbl (incM F JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)

  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ := fun p => by
    obtain ⟨c, hc⟩ := scalar_of_commute ψ hψ (omd p⁻¹ * omd₁ p)
      (fun l hl => by
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
        exact hS₁.adm p _ (hS.adm p⁻¹ l hl))
      (fun w φ hφ => by
        obtain ⟨w', rfl⟩ := dd.e.surjective w
        have e1 : schr ψ (dd.e w') = dd.rho ψ w' := rfl
        rw [e1, Module.End.mul_apply, Module.End.mul_apply]
        calc omd p⁻¹ (omd₁ p (dd.rho ψ w' φ)) = omd p⁻¹ (omd₁ p (dd₁.rho ψ w' φ)) := by rw [hrho]
          _ = omd p⁻¹ (dd₁.rho ψ (actB (cA σ) p w') (omd₁ p φ)) := by rw [hS₁.impl p w' φ hφ]
          _ = omd p⁻¹ (dd.rho ψ (actB (cA σ) p w') (omd₁ p φ)) := by rw [hrho]
          _ = dd.rho ψ (actB (cA σ) p⁻¹ (actB (cA σ) p w')) (omd p⁻¹ (omd₁ p φ)) :=
              hS.impl _ _ _ (hS₁.pres p φ hφ)
          _ = _ := by rw [actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (omd p) (hc φ hφ)
    rwa [Module.End.mul_apply, inv_mul, map_smul] at this

  choose cf hcf using key
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (cA σ) (dbl (incM F JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hS.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    simp only [LinearMap.proj_apply] at hf hf₁
    have h0 : omd p₀ (omd p₀⁻¹ φz) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / omd p _ 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ
  have hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ φ₀ hφ₀
    have e1 := hR l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd ψ z) φ) p t hpt _ hφ
    have e2 := hR₁ l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd₁ ψ z) φ) p t hpt _ hφ
    rw [← e2, hcf p _ hφ, inv_mul, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB ε hJ hdet c hcont hP
  have hcf1 : ∀ p, cf p = 1 := fun p => by
    rw [← hcv, hc1]; rfl
  intro g Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  have hb := GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ Φ hΦ φ₂ hφ₂
  have e := hres g gd hgd Φ hΦ φ₂ hφ₂
  have e₁ := hres₁ g gd hgd Φ hΦ φ₂ hφ₂
  rw [hcf gd _ hb, hcf1 gd, one_smul, e] at e₁
  funext x
  have := congrFun e₁ (Sum.elim x 0)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact mul_right_cancel₀ hφ₂0 this

theorem weil_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → ∀ om om₁ : Rep σ X W, M.IsWeil ψ χX χW om → M.IsWeil ψ χX χW om₁ → ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ = om₁ x Φ := by
  intro F E _ _ _ _ _ σ hσ n d X W M ψ χX χW hψ hX hXd hW hWd om om₁ h h₁ x Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d'₁, hd'₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_unique σ hσ X.J W.J (-1) eW hWd ψ hψ M.co χX _ _ hB hB₁
  have he : d'₁.e = d'.e := LinearEquiv.ext fun y => by rw [← Matrix.transpose_transpose y, hd'₁, hd']
  obtain ⟨e₁, f₁⟩ := d'₁
  obtain ⟨e₂, f₂⟩ := d'
  simp only at he
  subst he
  have uA := member_unique σ hσ W.J X.J 1 eX hXd ψ hψ _ χW _ _ hA hA₁
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : om (1, x.2) Φ = om₁ (1, x.2) Φ := uB x.2 Φ hΦ
  rw [h1]
  exact uA x.1 _ (hB₁.1.pres x.2 Φ hΦ)

end GlobalTheory.WeilSchUnique
