import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

def SiegelChar : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1

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

theorem member_tw (hT : TwEx) (hC : SiegelChar) (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (d d₁ : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ) (hr : RatRel d d₁) (hr' : RatRel d₁ d) (χ : Chr F E)
    (om om₁ : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (h₁ : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d₁ χ om₁) {e} (he : Tw ψ d d₁ e) :
    ∀ g, ∀ Φ ∈ schA F κ, e (om g Φ) = om₁ g (e Φ) := by
  obtain ⟨hS0, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  obtain ⟨ed, hd⟩ := hT F ψ hψ _ _ _ dd dd₁
  obtain ⟨ed₀, hd₀⟩ := hT F ψ hψ _ _ _ dd₁ dd
  obtain ⟨ed', hd', hl1, hl2⟩ := hd.exists_inv hψ hd₀ (hr.dbl hdd hdd₁) (hr'.dbl hdd₁ hdd)
  have inv_mul : ∀ (p : UG (cA σ) (dbl (incM F JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φy, hφy, hφy0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)
  obtain ⟨φz, hφz, hφz0⟩ : ∃ φ ∈ schA F (κ ⊕ κ), ed φ 0 ≠ 0 := ⟨ed' φy, hd'.maps _ hφy, by rwa [hl2 _ hφy]⟩
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have hsp₁ : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS₁.pres p φ hφ
  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ) := fun p => by
    obtain ⟨c, hc⟩ := schur hψ dd (omd p⁻¹ ∘ₗ ed' ∘ₗ omd₁ p ∘ₗ ed)
      (fun φ hφ => hsp _ _ (hd'.maps _ (hsp₁ _ _ (hd.maps φ hφ))))
      (fun l hl => hd.adm _ (hS₁.adm p _ (hd'.adm _ (hS.adm p⁻¹ l hl))))
      (fun w φ hφ => by
        have m1 := hd.maps φ hφ
        have m2 := hsp₁ p _ m1
        simp only [LinearMap.comp_apply]
        rw [hd.Heisenberg₂ w φ hφ, hS₁.impl p w _ m1, hd'.Heisenberg₂ _ _ m2, hS.impl _ _ _ (hd'.maps _ m2), actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (fun x => ed (omd p x)) (hc φ hφ)
    simp only [LinearMap.comp_apply, inv_mul, map_smul] at this
    rwa [hl2 _ (hsp₁ p _ (hd.maps φ hφ))] at this
  choose cf hcf using key
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ)) → c = cf p := fun p c hc => by
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
    have hf := hS.cont _ (hd.adm _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ))) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ (hd.maps _ hφ)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hf hf₁
    have h0 : ed (omd p₀ (omd p₀⁻¹ φz)) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / ed (omd p _) 0 = cf p
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
  have hinv₁ : ∀ z : Matrix (Fin a) (Fin b) (AE F E), ∀ φ ∈ schA F (κ ⊕ κ), l (dd₁.rho ψ (z * (diagCols (Fin b))ᵀ) φ) = l φ :=
    fun z φ hφ => by rw [dd_rho_diag hdd₁ ψ z]; exact hlinv _ _ φ hφ
  have hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ _ (hd'.maps φ₀ hφ₀)
    have e1 := hR (l ∘ₗ ed) (hd.adm l hl) (fun z φ hφ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hd.Heisenberg₂ _ φ hφ]
      exact hinv₁ z _ (hd.maps φ hφ)) p t hpt _ hφ
    have e2 := hR₁ l hl hinv₁ p t hpt _ (hd.maps _ hφ)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← e2, hcf p _ hφ, inv_mul, hl2 _ hφ₀, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := hC F E σ hσ b JB ε hJ hdet c hcont hP
  have hcf1 : ∀ p, cf p = 1 := fun p => by
    rw [← hcv, hc1]; rfl
  intro g Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g
  obtain ⟨e₂, h₂, hbox⟩ := box_compat hT hψ hr hdd hdd₁ he hd
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := h₂.ne
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hφ₂0
  have k := hcf gd _ (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ φ₂ hφ₂).1
  rw [hcf1 gd, one_smul, hres g gd hgd Φ hΦ φ₂ hφ₂, hbox Φ hΦ φ₂ hφ₂, hbox _ (hS0.pres g Φ hΦ) φ₂ hφ₂,
    hres₁ g gd hgd _ (he.maps Φ hΦ) _ (h₂.maps φ₂ hφ₂)] at k
  funext x
  have := congrFun k (Sum.elim x y)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact (mul_right_cancel₀ hy this).symm

theorem pair_tw (hT : TwEx) (hC : SiegelChar) (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    (M M₁ : Model σ X W) {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} (hψ : IsStd ψ) (hX : ∀ i j, σ (X.J j i) = X.J i j)
    (hXd : X.J.det ≠ 0) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0) (hr : RatRel M.co M₁.co) (hr' : RatRel M₁.co M.co)
    {om om₁ : Rep σ X W} (h : M.IsWeil ψ χX χW om) (h₁ : M₁.IsWeil ψ χX χW om₁) {e} (he : Tw ψ M.co M₁.co e) :
    ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro x Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d₁, hd₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_tw hT hC σ hσ X.J W.J (-1) eW hWd ψ hψ M.co M₁.co hr hr' χX _ _ hB hB₁ he
  have r1 : RatRel d' d₁ := fun y z => by
    obtain ⟨w, y', z', h1, h2⟩ := hr y z
    exact ⟨wᵀ, y', z', (hd' w).trans h1, (hd₁ w).trans h2⟩
  have r2 : RatRel d₁ d' := fun y z => by
    obtain ⟨w, y', z', h1, h2⟩ := hr' y z
    exact ⟨wᵀ, y', z', (hd₁ w).trans h1, (hd' w).trans h2⟩
  have he' : Tw ψ d' d₁ e := ⟨he.maps, fun w Φ hΦ => by
    have := he.Heisenberg₂ wᵀ Φ hΦ
    rw [Darboux.rho, Darboux.rho, ← hd', ← hd₁, Matrix.transpose_transpose] at this
    exact this, he.adm, he.ne⟩
  have uA := member_tw hT hC σ hσ W.J X.J 1 eX hXd ψ hψ d' d₁ r1 r2 χW _ _ hA hA₁ he'
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : e (om (1, x.2) Φ) = om₁ (1, x.2) (e Φ) := uB x.2 Φ hΦ
  rw [← h1]
  exact uA x.1 _ (hB.1.pres x.2 Φ hΦ)

end PositivityTheory.ThKF0

end
