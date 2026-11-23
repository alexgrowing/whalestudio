import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProductMap

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ReBase

section Proj

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def prM (e : R) (he : e * e = e) (ι : Type) [Fintype ι] [DecidableEq ι] : Matrix ι ι A →* Matrix ι ι A :=
  _root_.UpperTheory.Reformulated.B.IdempotentMatrixMonoidHom.prM e he ι

theorem prM_apply (e : R) (he : e * e = e) (M : Matrix ι ι A) : prM e he ι M = e • M + (1 - e) • 1 := rfl

def prU (c : A →ₐ[R] A) (J : Matrix ι ι A) (e : R) (he : e * e = e) : UG c J →* UG c J :=
  ((Units.map (prM e he ι)).comp (UG c J).subtype).codRestrict _ fun g => by
    have hg : g.1.1ᵀ * J * g.1.1.map c = J := g.2
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
    show (e • g.1.1 + (1 - e) • 1)ᵀ * J * (e • g.1.1 + (1 - e) • (1 : Matrix ι ι A)).map c = J
    have hm : (e • g.1.1 + (1 - e) • (1 : Matrix ι ι A)).map c = e • g.1.1.map c + (1 - e) • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, he, h1, h2, h3,
      zero_smul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hg]
    rw [← add_smul, add_sub_cancel, one_smul]

theorem prU_val (c : A →ₐ[R] A) (J : Matrix ι ι A) (e : R) (he : e * e = e) (g : UG c J) :
    (prU c J e he g).1.1 = e • g.1.1 + (1 - e) • 1 := rfl

theorem continuous_prU [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul R A] (c : A →ₐ[R] A)
    (J : Matrix ι ι A) (e : R) (he : e * e = e) : Continuous (prU c J e he) := by
  refine Continuous.subtype_mk ?_ _
  have h : Continuous (prM (A := A) e he ι) := (continuous_id.const_smul e).add continuous_const
  exact (Continuous.units_map _ h).comp continuous_subtype_val

theorem smul_det_prM (e : R) (he : e * e = e) (M : Matrix ι ι A) {u : R} (hu : u * e = 0) :
    u • ((prM e he ι M).det - 1) = 0 := by
  let I : Ideal A := Ideal.span {algebraMap R A e}
  have h0 : Ideal.Quotient.mk I (algebraMap R A e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have h1 : (Ideal.Quotient.mk I).mapMatrix (prM e he ι M) = 1 := by
    ext i j
    simp only [prM_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
    simp only [map_add, Algebra.smul_def, map_mul, map_sub, h0, map_one, Matrix.one_apply]
    split_ifs <;> simp
  have h2 : (prM e he ι M).det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, h1, Matrix.det_one, map_one, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  rw [← hy, Algebra.smul_def, mul_left_comm, ← map_mul, hu, map_zero, mul_zero]

theorem prM_mul {κ : Type} [Fintype κ] [DecidableEq κ] (e : R) (he : e * e = e) {M : Matrix ι ι A} {N : Matrix κ κ A}
    {D : Matrix ι κ A} (h : M * D = D * N) : prM e he ι M * D = D * prM e he κ N := by
  rw [prM_apply, prM_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, h, Matrix.one_mul, Matrix.mul_one]

theorem prM_fromBlocks (e : R) (he : e * e = e) {M : Matrix ι ι A} (h : (1 - e) • (M - 1) = 0) :
    prM e he (ι ⊕ ι) (Matrix.fromBlocks M 0 0 1) = Matrix.fromBlocks M 0 0 1 := by
  rw [smul_sub, sub_eq_zero] at h
  rw [prM_apply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
    ← add_smul e (1 - e) (1 : Matrix ι ι A), ← h]
  simp only [← add_smul, add_sub_cancel, one_smul]

end Proj

open GlobalTheory.WeilSchUnique

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

variable (F) in

def eInf : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem eInf_mul : eInf F * eInf F = eInf F := Prod.ext (one_mul (1 : InfiniteAdeleRing F)) (zero_mul (0 : FiniteAdeleRing (𝓞 F) F))

theorem mul_eInf {u : AF F} (hu : evI F u = 0) : u * eInf F = 0 := by
  have h0 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · show u.1 * 1 = 0
    rw [h0, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem evI_one_sub_eInf : evI F (1 - eInf F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 - 1) = 0
  rw [sub_self, map_zero]

theorem member_arch_eq (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ) (χ χ₁ : Chr F E)
    (hχ : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χ z = χ₁ z)
    (om om₁ : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (h₁ : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ₁ om₁) :
    ∀ g, At (evI F) (g.1.1 - 1) → ∀ Φ ∈ schA F κ, om g Φ = om₁ g Φ := by
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
        χ (Matrix.GeneralLinearGroup.det t) = χ₁ (Matrix.GeneralLinearGroup.det t) → c p = 1 := fun p t hpt hχt => by
    have hφ := hsp p⁻¹ φ₀ hφ₀
    have e1 := hR l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd ψ z) φ) p t hpt _ hφ
    have e2 := hR₁ l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd₁ ψ z) φ) p t hpt _ hφ
    rw [hχt, ← e2, hcf p _ hφ, inv_mul, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  let π := prU (cA σ) (dbl (incM F JB)) (eInf F) eInf_mul
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB ε hJ hdet (c.comp π) (hcont.comp (continuous_prU _ _ _ _)) (fun p t hpt => by
    refine hP (π p) (Units.map (prM (eInf F) eInf_mul (Fin b)) t) ?_ (hχ _ fun u hu => ?_)
    · exact prM_mul (eInf F) eInf_mul hpt
    · exact smul_det_prM (eInf F) eInf_mul t.1 (mul_eInf hu))
  intro g hg Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g
  have hπ : π gd = gd := by
    refine Subtype.ext (Units.ext ?_)
    have h0 : (1 - eInf F) • (g.1.1 - 1) = 0 := hg _ evI_one_sub_eInf
    show prM (eInf F) eInf_mul _ gd.1.1 = gd.1.1
    rw [hgd]
    exact prM_fromBlocks _ _ h0
  have hcf1 : cf gd = 1 := by
    have := congrArg (fun f => f gd) hc1
    simp only [MonoidHom.comp_apply, hπ, MonoidHom.one_apply] at this
    rw [← hcv, this]; rfl
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  have hb := GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ Φ hΦ φ₂ hφ₂
  have e := hres g gd hgd Φ hΦ φ₂ hφ₂
  have e₁ := hres₁ g gd hgd Φ hΦ φ₂ hφ₂
  rw [hcf gd _ hb, hcf1, one_smul, e] at e₁
  funext x
  have := congrFun e₁ (Sum.elim x 0)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact mul_right_cancel₀ hφ₂0 this

theorem weil_arch_eq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {ψ : AddChar (AF F) ℂ} {χX χW χX₁ χW₁ : Chr F E} (hψ : IsStd ψ) (hX : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0)
    (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (hχX : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χX z = χX₁ z)
    (hχW : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χW z = χW₁ z)
    {om om₁ : Rep σ X W} (h : M.IsWeil ψ χX χW om) (h₁ : M.IsWeil ψ χX₁ χW₁ om₁)
    {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) {k : UA σ W.J} (hk : k ∈ UAt σ W (evI F)) :
    ∀ Φ ∈ schA F (Fin n × Fin d), om (g, k) Φ = om₁ (g, k) Φ := by
  intro Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d'₁, hd'₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_arch_eq σ hσ X.J W.J (-1) eW hWd ψ hψ M.co χX χX₁ hχX _ _ hB hB₁
  have he : d'₁.e = d'.e := LinearEquiv.ext fun y => by rw [← Matrix.transpose_transpose y, hd'₁, hd']
  obtain ⟨e₁, f₁⟩ := d'₁
  obtain ⟨e₂, f₂⟩ := d'
  simp only at he
  subst he
  have uA := member_arch_eq σ hσ W.J X.J 1 eX hXd ψ hψ _ χW χW₁ hχW _ _ hA hA₁
  have hx : ((g, k) : UA σ X.J × UA σ W.J) = (g, 1) * (1, k) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : om (1, k) Φ = om₁ (1, k) Φ := uB k hk Φ hΦ
  rw [h1]
  exact uA g hg _ (hB₁.1.pres k Φ hΦ)

end GlobalTheory.ReBase

end
