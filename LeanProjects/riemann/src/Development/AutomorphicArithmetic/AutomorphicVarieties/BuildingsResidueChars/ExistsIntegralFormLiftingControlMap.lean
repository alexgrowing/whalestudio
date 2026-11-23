import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem control_map_translate_trace {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type} [CommRing O]
    [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (F : Fin m → X.Fn Ω (W.d + 1))
    (g : Ga × Gp) (b : Gp) (i : Fin m) :
    X.ctrl m W F (g * (1, b)) i =
      ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ (X.rpF Ω (W.d + 1) m b F i g)) j := by
  rw [Frame.ctrl_apply, Frame.unt_apply]
  show _ = ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ F i (g * (1, b))) j
  rw [Prod.snd_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, map_inv]
  rfl

theorem UpperTheory.exists_integral_form_lifting_controlMap :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ) (θ : X.I.T →* Oˣ), Function.Injective (algebraMap O Ω) → (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) → ∀ F ∈ X.ClO W τ U c φ, F ∈ X.Lat m W (mIm O Ω 0) → ∃ f ∈ X.Sp τ θ U, X.mapFn (B := Ω) f = X.ctrl m W F ∧ ∀ k c' : ℕ, c ≤ c' → (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k, W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) → ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c θ hinj hθ F hF hL
  have hL' : ∀ i g k, X.unt m W F i g k ∈ mIm O Ω 0 := fun i g k => hL i g k
  have hv : ∀ i g k, ∃ a : O, algebraMap O Ω a = X.unt m W F i g k := by
    intro i g k
    obtain ⟨a, -, ha⟩ := mem_mIm.1 (hL' i g k)
    exact ⟨a, ha⟩
  choose v hv0 using hv
  have hu : ∀ i g j, ((W.ξ g.2)⁻¹.val *ᵥ F i g) j = algebraMap O Ω (v i g j) := by
    intro i g j
    rw [hv0, Frame.unt_apply]
  obtain ⟨f, hf⟩ : ∃ f : X.Fn O m, ∀ g i, algebraMap O Ω (f g i) = X.ctrl m W F g i :=
    ⟨fun g i => v i g 0, fun g i => by rw [Frame.ctrl_apply, hv0]⟩
  have hf0 : ∀ g i, algebraMap O Ω (f g i) = algebraMap O Ω (v i g 0) := by
    intro g i
    rw [hf, Frame.ctrl_apply, hv0]
  have hs : ∀ (b : Gp) (a : Ω), X.rpF Ω (W.d + 1) m b F = a • F → ∀ g i,
      algebraMap O Ω (f (g * (1, b)) i) = a * ∑ j, (W.ξ b⁻¹).val 0 j * algebraMap O Ω (v i g j) := by
    intro b a hb g i
    rw [hf, control_map_translate_trace, hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul, hu]
    ring
  have hE := hF.2
  have hUF := hF.1.2
  have hA : ∀ i (γ : Γ) (g : Ga × Gp), F i (X.glob γ * g) = (W.ξ (X.glob γ).2).val *ᵥ F i g :=
    fun i γ g => hF.1.1 i (Set.mem_univ i) γ g
  have key : ∀ k c' : ℕ, c ≤ c' → (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k, W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) → ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k := by
    intro k c' hc hξ y hy g _ i _
    have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hc hy
    choose a ha hae using fun j => hξ y⁻¹ (inv_mem hy) 0 j
    have h1 : f (g * (1, y)) i - f g i = ∑ j, a j * v i g j := by
      apply hinj
      rw [map_sub, hs y 1 (by rw [one_smul]; exact hE.2.1 y hyc) g i, hf0, one_mul, map_sum]
      simp only [hae, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
      ring
    show f (g * (1, y)) i - f g i ∈ maximalIdeal O ^ k
    rw [h1]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (ha j)
  refine ⟨f, ?_, ?_, key⟩
  · refine Submodule.mem_inf.2 ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro γ g
      funext i
      apply hinj
      rw [hf, hf, Frame.ctrl_apply, Frame.ctrl_apply, Frame.unt_apply, Frame.unt_apply, hA, Prod.snd_mul, map_mul,
        Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    · intro u hu'
      funext g i
      apply hinj
      show algebraMap O Ω (f (g * (1, u)) i) = algebraMap O Ω (f g i)
      rw [hs u 1 (by rw [one_smul]; exact hE.1 u hu') g i, hf0, one_mul]
      simp only [W.row_N _ (X.I.N_le (inv_mem hu')), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · intro t
      funext g i
      apply hinj
      show algebraMap O Ω (f (g * (1, (t : Gp))) i) = algebraMap O Ω (((θ t)⁻¹ : Oˣ) * f g i)
      rw [hs (t : Gp) _ (hE.2.2 t) g i, map_mul, hf0]
      have hr : ∀ j, (W.ξ (t : Gp)⁻¹).val 0 j = if j = 0 then (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) else 0 :=
        fun j => W.torusAction ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ j
      have hχ : (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) = (W.χ ⟨t, X.I.T_le t.2⟩ : Ω)⁻¹ := by
        rw [← Units.val_inv_eq_inv_val, ← map_inv]
        rfl
      have hθ' : algebraMap O Ω (((θ t)⁻¹ : Oˣ) : O) = (algebraMap O Ω (θ t))⁻¹ := map_units_inv (algebraMap O Ω) (θ t)
      simp only [hr, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hχ, hθ', hθ t]
      simp only [MonoidHom.comp_apply, Units.coe_map, Units.val_inv_eq_inv_val, MonoidHom.coe_coe]
      rw [mul_inv, mul_assoc]
      rfl
    · intro k
      obtain ⟨c1, hc1⟩ := W.cont_Nm k
      refine ⟨max c c1, fun y hy g i => ?_⟩
      have h := key k (max c c1) (le_max_left _ _)
        (fun y hy => hc1 y (X.I.Nm_anti (le_max_right _ _) hy)) y hy g (Set.mem_univ _) i (Set.mem_univ _)
      exact h
    · intro u hu'
      funext g i
      apply hinj
      rw [Frame.ra_apply, hf, ← hUF u hu',
        (ctrlEq Γ Ga Gp X O Ω W m ((GeneralLinearGroup.map (algebraMap O Ω)).comp τ)).1 u F, Frame.ra_apply]
      simp [Matrix.mulVec, dotProduct, hf]
  · funext g i
    exact hf g i
