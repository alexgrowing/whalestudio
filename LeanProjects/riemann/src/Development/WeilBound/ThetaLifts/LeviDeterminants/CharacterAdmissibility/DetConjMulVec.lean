import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.BoxCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement

noncomputable section

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace PositivityTheory.ThKF0.Chr

open Matrix GlobalTheory.WeilM

section Char

variable {R : Type} [CommRing R] [Invertible (2 : R)] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}

theorem Ax.exists_char (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e) {G : Type} [Group G]
    [TopologicalSpace G] {om : G →* Module.End ℂ ((κ → R) → ℂ)} {om₁ : G →* Module.End ℂ ((κ₁ → R) → ℂ)}
    (p : ∀ g, ∀ φ ∈ C.sp κ, om g φ ∈ C.sp κ) (a : ∀ g, ∀ l ∈ C.adm κ, l ∘ₗ om g ∈ C.adm κ)
    (a₁ : ∀ g, ∀ l ∈ C.adm κ₁, l ∘ₗ om₁ g ∈ C.adm κ₁) (c : IsContOn C om) (c₁ : IsContOn C om₁)
    (hl : ∀ g w w₁, Rel S j w w₁ → ∃ w' w₁', Rel S j w' w₁' ∧ (∀ φ ∈ C.sp κ, om g (schr ψ w φ) = schr ψ w' (om g φ)) ∧
      ∀ φ ∈ C.sp κ₁, om₁ g⁻¹ (schr ψ w₁' φ) = schr ψ w₁ (om₁ g⁻¹ φ)) :
    ∃ A : G →* ℂˣ, Continuous A ∧ ∀ g, ∀ φ ∈ C.sp κ, e (om g φ) = (A g : ℂ) • om₁ g (e φ) := by
  have inv : ∀ g φ, om₁ g (om₁ g⁻¹ φ) = φ := fun g φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have inv' : ∀ g φ, om g (om g⁻¹ φ) = φ := fun g φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have key : ∀ g, ∃ b : ℂ, ∀ φ ∈ C.sp κ, e (om g φ) = b • om₁ g (e φ) := fun g => by
    obtain ⟨b, hb⟩ := h.uniq hS hj he (e' := om₁ g⁻¹ ∘ₗ e ∘ₗ om g) (fun w w₁ hw φ hφ => by
      obtain ⟨w', w₁', r, h1, h2⟩ := hl g w w₁ hw
      show om₁ g⁻¹ (e (om g _)) = schr ψ w₁ (om₁ g⁻¹ (e (om g φ)))
      rw [h1 φ hφ, he.law _ _ r _ (p g φ hφ), h2 _ (he.maps _ (p g φ hφ))]) (a g _ (he.adm _ (a₁ g⁻¹ _ (h.ev0 _))))
    exact ⟨b, fun φ hφ => by rw [← map_smul, ← hb φ hφ]; exact (inv g _).symm⟩
  choose b hb using key
  obtain ⟨φ₀, h₀, hne⟩ := (h.E_cyc hS hj he).ne h
  have hne : e φ₀ 0 ≠ 0 := hne
  have uq : ∀ g (x : ℂ), (∀ φ ∈ C.sp κ, e (om g φ) = x • om₁ g (e φ)) → x = b g := fun g x hx => by
    have e1 := congrArg (om₁ g⁻¹) ((hx φ₀ h₀).symm.trans (hb g φ₀ h₀))
    have i2 := inv g⁻¹ (e φ₀)
    rw [inv_inv] at i2
    rw [map_smul, map_smul, i2] at e1
    exact mul_right_cancel₀ hne (congrFun e1 0)
  let B : G →* ℂ :=
    { toFun := b
      map_one' := (uq 1 1 fun φ _ => by simp).symm
      map_mul' := fun g g' => (uq _ _ fun φ hφ => by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb g _ (p g' φ hφ), hb g' φ hφ, map_smul,
          smul_smul]).symm }
  refine ⟨B.toHomUnits, ?_, hb⟩
  rw [Units.isEmbedding_val₀.continuous_iff]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hφ := p g₀⁻¹ φ₀ h₀
  have c1 := c _ (he.adm _ (h.ev0 _)) _ hφ
  have c2 := c₁ _ (h.ev0 _) _ (he.maps _ hφ)
  have h0 : Chr.ev0 R κ₁ (om₁ g₀ (e (om g₀⁻¹ φ₀))) ≠ 0 := fun e0 => hne (by
    have := congrFun (hb g₀ _ hφ) 0
    rw [inv'] at this
    rw [this, Pi.smul_apply, show om₁ g₀ (e (om g₀⁻¹ φ₀)) 0 = 0 from e0, smul_zero])
  refine (c1.continuousAt.div c2.continuousAt h0).congr ?_
  filter_upwards [c2.continuousAt.eventually_ne h0] with g hg
  show Chr.ev0 R κ₁ (e (om g _)) / _ = b g
  rw [hb g _ hφ, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hg]

end Char

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α α₁ β κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype β] [DecidableEq β]
  [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {JA₁ : Matrix α₁ α₁ E} {J : Matrix β β E} {ι : Matrix α α₁ E} {x y : α → E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}

omit [Invertible (2 : R)] in
theorem det_conj_mulVec [Module.Free R E] [Module.Finite R E] {ρ : Type} (θ : (β → E) ≃ₗ[R] (ρ → R)) (t : GL β E) :
    ∃ g : (ρ → R) ≃ₗ[R] (ρ → R), (∀ b, g (θ b) = θ (t.1 *ᵥ b)) ∧
      LinearEquiv.det g = Units.map (Algebra.norm R : E →* R) (GeneralLinearGroup.det t) := by
  let τ : (β → E) ≃ₗ[E] (β → E) := LinearEquiv.ofLinear (toLin' t.1) (toLin' (t⁻¹).1)
    (by rw [← toLin'_mul, t.mul_inv, toLin'_one]) (by rw [← toLin'_mul, t.inv_mul, toLin'_one])
  refine ⟨θ.symm ≪≫ₗ τ.restrictScalars R ≪≫ₗ θ, fun b => by simp [τ], Units.ext ?_⟩
  rw [LinearEquiv.coe_det]
  have : ((θ.symm ≪≫ₗ τ.restrictScalars R ≪≫ₗ θ : (ρ → R) ≃ₗ[R] (ρ → R)) : (ρ → R) →ₗ[R] (ρ → R)) =
      (θ : (β → E) →ₗ[R] (ρ → R)) ∘ₗ (toLin' t.1).restrictScalars R ∘ₗ (θ.symm : (ρ → R) →ₗ[R] (β → E)) := rfl
  rw [this, LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rfl

theorem TA [TopologicalSpace R] [TopologicalSpace E] [IsModuleTopology R E] [Module.Free R E] [Module.Finite R E]
    (h : Ax C ψ) (hI : AxInt C) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    (hcard : Fintype.card α = Fintype.card α₁ + 2)
    {d : Darboux (symp c ξ JA J) κ} {d₁ : Darboux (symp c ξ JA₁ J) κ₁}
    (hrel : ∀ u z, Rel S j (d.e u) (d₁.e z) ↔ ∃ b : β → E, u = ι * z + vecMulVec x b)
    {ρ : Type} [Fintype ρ] {i : ρ → κ} (hi : Function.Injective i) (hij : ∀ k, (∃ a, i a = k) ↔ ¬ ∃ a, j a = k)
    (θ : (β → E) ≃ₗ[R] (ρ → R)) (hθ : ∀ b, S (d.e (vecMulVec y b)) = (Function.extend i (θ b) 0, 0)) {χ : Eˣ →* Circle}
    {om : UG c J →* Module.End ℂ ((κ → R) → ℂ)} {om₁ : UG c J →* Module.End ℂ ((κ₁ → R) → ℂ)}
    (hW : IsUWeilB c C ψ ξ JA J d χ om) (hW₁ : IsUWeilB c C ψ ξ JA₁ J d₁ χ om₁)
    (hch : ∀ a : UG c (dbl J) →* ℂˣ, Continuous a → (∀ (p : UG c (dbl J)) (t : GL β E),
      p.1.1 * diagCols (E := E) β = diagCols (E := E) β * t.1 → a p = 1) → a = 1)
    (g : UG c J) : ∀ φ ∈ C.sp κ, e (om g φ) = om₁ g (e φ) := by
  obtain ⟨hs₀, dd, omd, hd, ⟨-, hs, hr⟩, hb⟩ := hW
  obtain ⟨hs₁₀, dd₁, omd₁, hd₁, ⟨-, hs₁, hr₁⟩, hb₁⟩ := hW₁
  have hj2 := hj.sumMap hj
  have hrel2 : ∀ u z, Rel (dbS S) (Sum.map j j) (dd.e u) (dd₁.e z) ↔ ∃ b : β ⊕ β → E, u = ι * z + vecMulVec x b := fun u z => by
    rw [← fromCols_toCols u, ← fromCols_toCols z, hd, hd₁]
    generalize u.toCols₁ = u₁, u.toCols₂ = u₂, z.toCols₁ = z₁, z.toCols₂ = z₂
    have e1 : ∀ b : β ⊕ β → E, ι * fromCols z₁ z₂ + vecMulVec x b =
        fromCols (ι * z₁ + vecMulVec x (b ∘ Sum.inl)) (ι * z₂ + vecMulVec x (b ∘ Sum.inr)) := fun b => by
      rw [mul_fromCols]
      ext i (k | k) <;> rfl
    refine (rel_dv hj).trans ⟨fun ⟨p, q⟩ => ?_, fun ⟨b, hb⟩ => ?_⟩
    · obtain ⟨b₁, rfl⟩ := (hrel _ _).1 p
      obtain ⟨b₂, rfl⟩ := (hrel _ _).1 q
      exact ⟨Sum.elim b₁ b₂, (e1 (Sum.elim b₁ b₂)).symm⟩
    · rw [e1, fromCols_ext_iff] at hb
      exact ⟨(hrel _ _).2 ⟨_, hb.1⟩, (hrel _ _).2 ⟨_, hb.2⟩⟩
  obtain ⟨E₂, hE⟩ := h.exists_E hS.dbS hj2
  obtain ⟨l, hl, hinv, hcyc⟩ := h.exists_diag κ₁
  have hdiag : ∀ z : Matrix α β E, dd.e (z * (diagCols (E := E) β)ᵀ) = dv (d.e z) (d.e z) := fun z => by
    rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one, hd]
    rfl
  have hdiag₁ : ∀ z : Matrix α₁ β E, dd₁.e (z * (diagCols (E := E) β)ᵀ) = dv (d₁.e z) (d₁.e z) := fun z => by
    rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one, hd₁]
    rfl
  obtain ⟨A, hAc, hA⟩ := h.exists_char hS.dbS hj2 hE hs.pres hs.adm hs₁.adm hs.cont hs₁.cont fun p w w₁ hw => by
    obtain ⟨u, rfl⟩ := dd.e.surjective w
    obtain ⟨z, rfl⟩ := dd₁.e.surjective w₁
    obtain ⟨b, rfl⟩ := (hrel2 u z).1 hw
    refine ⟨_, dd₁.e (actB c p z), (hrel2 (actB c p (ι * z + vecMulVec x b)) _).2 ⟨p.1.1 *ᵥ b, ?_⟩, hs.impl p _, fun φ hφ => ?_⟩
    · simp only [actB, Matrix.add_mul, Matrix.mul_assoc, vecMulVec_mul, vecMul_transpose]
    · refine (hs₁.impl p⁻¹ _ _ hφ).trans ?_
      rw [show actB c p⁻¹ (actB c p z) = z by simp [actB, Matrix.mul_assoc, ← transpose_mul]]
      rfl
  obtain ⟨L, hL, ⟨Ψ, hΨ, hne⟩, hLi, hLO⟩ := h.exists_avg hI hS hj hE hl hinv hcyc ρ i hi hij
  have hA1 : A = 1 := hch A hAc fun p t hp => by
    obtain ⟨g, hg, hdet⟩ := det_conj_mulVec θ t
    have e1 := hr L hL (fun z φ hφ => by rw [Darboux.rho, hdiag, hLi _ _ hφ]) p t hp Ψ hΨ
    have r1 := hr₁ l hl (fun z φ hφ => by rw [Darboux.rho, hdiag₁, hinv _ _ hφ]) p t hp
    set m : ℝ := (C.modu (Units.map (Algebra.norm R : E →* R) (GeneralLinearGroup.det t)) : ℝ) with hm
    have hm0 : 0 < m := by
      rw [hm]; exact_mod_cast pos_iff_ne_zero.2 ((Group.isUnit _).map C.modu).ne_zero
    have hf : ∀ n : ℕ, (χ (GeneralLinearGroup.det t) : ℂ) * ((m ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := fun n =>
      mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hm0 _).ne')
    have hy : ∀ b, S.symm (Function.extend i (θ b) 0, 0) = d.e (vecMulVec y b) := fun b => by
      rw [← hθ, S.symm_apply_apply]
    have e2 := hLO (omd p) (A p * ((χ (GeneralLinearGroup.det t) : ℂ) * ((m ^ ((Fintype.card α₁ : ℝ) / 2) : ℝ) : ℂ))) g
      (mul_ne_zero (A p).ne_zero (hf _)) (hs.pres p) (fun u φ hφ => by
        obtain ⟨b, rfl⟩ := θ.surjective u
        rw [hg, hy, hy, ← hdiag, ← hdiag]
        refine (hs.impl p _ φ hφ).trans ?_
        rw [actB, Matrix.mul_assoc, ← transpose_mul, hp,
          transpose_mul, ← Matrix.mul_assoc, vecMulVec_mul, vecMul_transpose]
        rfl) (fun φ hφ => by rw [hA p φ hφ, map_smul, r1 _ (hE.maps φ hφ), smul_eq_mul]; ring) Ψ hΨ
    have e3 := mul_right_cancel₀ hne (e1.symm.trans e2)
    have e4 : m ^ ((Fintype.card α : ℝ) / 2) = m ^ ((Fintype.card α₁ : ℝ) / 2) * m := by
      rw [← Real.rpow_add_one hm0.ne', hcard]
      congr 1
      push_cast
      ring
    rw [hdet, ← hm, mul_assoc, mul_assoc, ← Complex.ofReal_mul, ← e4] at e3
    exact Units.ext ((mul_eq_right₀ (hf _)).1 e3.symm)
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one R E c β J g
  obtain ⟨φ₁, h₁, φ₂, h₂, hne₂⟩ := h.box_ne hS hj hE hcyc
  obtain ⟨B, hB, hBe⟩ := h.box_E hS hj he hE φ₂ h₂
  have hB0 : B ≠ 0 := fun e0 => hne₂ (by
    rw [hBe _ h₁, e0, show boxFun (e φ₁) (0 : (κ₁ → R) → ℂ) = 0 from funext fun x => mul_zero _, map_zero])
  intro φ hφ
  have e6 := hA gd _ (h.box _ _ _ hφ _ h₂)
  rw [hA1, hb g gd hgd _ hφ _ h₂, hBe _ (hs₀.pres _ _ hφ), hBe _ hφ, hb₁ g gd hgd _ (he.maps _ hφ) _ hB] at e6
  exact box_cancel hB0 (e6.trans (one_smul _ _))

theorem TA' [TopologicalSpace R] [TopologicalSpace E] [IsModuleTopology R E] [Module.Free R E] [Module.Finite R E]
    (h : Ax C ψ) (hI : AxInt C) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    (hcard : Fintype.card α = Fintype.card α₁ + 2)
    {d : Darboux (symp c ξ JA J) κ} {d₁ : Darboux (symp c ξ JA₁ J) κ₁}
    (hrel : ∀ u z, Rel S j (d.e u) (d₁.e z) ↔ ∃ b : β → E, u = ι * z + vecMulVec x b)
    (hy : ∀ b, (S (d.e (vecMulVec y b))).2 = 0 ∧ (S (d.e (vecMulVec y b))).1 ∘ j = 0)
    (hy0 : ∀ b : β → E, vecMulVec y b = 0 → b = 0)
    (hsp : ∀ u : Matrix α β E, ∃ z a b, u = ι * z + vecMulVec x a + vecMulVec y b) {χ : Eˣ →* Circle}
    {om : UG c J →* Module.End ℂ ((κ → R) → ℂ)} {om₁ : UG c J →* Module.End ℂ ((κ₁ → R) → ℂ)}
    (hW : IsUWeilB c C ψ ξ JA J d χ om) (hW₁ : IsUWeilB c C ψ ξ JA₁ J d₁ χ om₁)
    (hch : ∀ a : UG c (dbl J) →* ℂˣ, Continuous a → (∀ (p : UG c (dbl J)) (t : GL β E),
      p.1.1 * diagCols (E := E) β = diagCols (E := E) β * t.1 → a p = 1) → a = 1)
    (g : UG c J) : ∀ φ ∈ C.sp κ, e (om g φ) = om₁ g (e φ) := by
  classical
  let Y : (β → E) →ₗ[R] Matrix α β E :=
    { toFun := vecMulVec y
      map_add' := fun a b => by ext i k; simp [vecMulVec_apply, mul_add]
      map_smul' := fun a b => by ext i k; simp [vecMulVec_apply] }
  let θ₀ : (β → E) →ₗ[R] ({k // ¬ ∃ a, j a = k} → R) :=
    LinearMap.funLeft R R Subtype.val ∘ₗ LinearMap.fst R _ _ ∘ₗ S.toLinearMap ∘ₗ d.e.toLinearMap ∘ₗ Y
  have h0 : ∀ b k, θ₀ b k = (S (d.e (vecMulVec y b))).1 k.1 := fun _ _ => rfl
  have hθ : ∀ b, S (d.e (vecMulVec y b)) = (Function.extend Subtype.val (θ₀ b) 0, 0) := fun b => by
    refine Prod.ext (funext fun k => ?_) (hy b).1
    by_cases hk : ∃ a, j a = k
    · refine Eq.trans ?_ (Function.extend_apply' (f := (Subtype.val : {k // ¬ ∃ a, j a = k} → κ)) (θ₀ b) (0 : κ → R) k
        fun ⟨a, ha⟩ => a.2 (ha ▸ hk)).symm
      obtain ⟨a, rfl⟩ := hk
      exact congrFun (hy b).2 a
    · exact (Subtype.val_injective.extend_apply (θ₀ b) 0 ⟨k, hk⟩).symm
  have hb : Function.Bijective θ₀ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun b hb => hy0 b ?_, fun v => ?_⟩
    · have := hθ b
      rw [hb, extend_zero' Subtype.val_injective] at this
      exact d.e.map_eq_zero_iff.1 (S.map_eq_zero_iff.1 this)
    · obtain ⟨z, a, b, hu⟩ := hsp (d.e.symm (S.symm (Function.extend Subtype.val v 0, 0)))
      refine ⟨b, funext fun k => ?_⟩
      have e1 := congrFun (congrArg (fun u => (S (d.e u)).1) hu) k.1
      have e2 := congrFun ((hrel _ z).2 ⟨a, rfl⟩).1 k.1
      rw [Function.extend_apply' _ _ _ k.2] at e2
      simp only [LinearEquiv.apply_symm_apply, Subtype.val_injective.extend_apply] at e1
      rw [map_add, map_add, Prod.fst_add, Pi.add_apply] at e1
      exact (e1.trans ((congrArg (· + _) e2).trans (zero_add _))).symm
  exact TA h hI hS hj he hcard hrel Subtype.val_injective (fun k => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hk => ⟨⟨k, hk⟩, rfl⟩⟩)
    (LinearEquiv.ofBijective θ₀ hb) hθ hW hW₁ hch g

end PositivityTheory.ThKF0.Chr
