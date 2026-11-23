import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.MackeyTwo

open UpperTheory.V.Sd.S2 UpperTheory.V.AlgebraTools UpperTheory.V.Af
open scoped Matrix

section

variable {k : Type} [Field k]

private noncomputable def pX (α β : kˣ) : (Fin 2 → k) →ₗ[k] (Fin 4 → k) where
  toFun a := ![a 1 / β, a 0 / α, -(a 1 / β), a 0 / α]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

private noncomputable def pY : (Fin 2 → k) →ₗ[k] (Fin 4 → k) where
  toFun b := ![b 1, -b 0, b 1, b 0]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp

private theorem pX_apply (α β : kˣ) (a : Fin 2 → k) : pX α β a = ![a 1 / β, a 0 / α, -(a 1 / β), a 0 / α] := rfl

private theorem pY_apply (b : Fin 2 → k) : pY b = ![b 1, -b 0, b 1, b 0] := rfl

private theorem pX_inj (α β : kˣ) : Function.Injective (pX α β) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [pX_apply] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

private theorem pY_inj : Function.Injective (pY (k := k)) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 3
  simp [pY_apply] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

private theorem mix_pX (h2 : (2 : k) ≠ 0) (α β : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) (a : Fin 2 → k) :
    mix (β / α) A B *ᵥ pX α β a = pX α β (A *ᵥ a) := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  ext i
  fin_cases i <;>
    simp [mix, pX_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem mix_pY (h2 : (2 : k) ≠ 0) (γ : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) (a : Fin 2 → k) :
    mix γ A B *ᵥ pY a = pY (B *ᵥ a) := by
  have hγ := γ.ne_zero
  ext i
  fin_cases i <;>
    simp [mix, pY_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem diag_pX (α β : kˣ) (a : Fin 2 → k) :
    Matrix.diagonal ![(β : k), -(α : k), -(β : k), (α : k)] *ᵥ pX α β a = pY a := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  ext i
  fin_cases i <;> simp [pX_apply, pY_apply, Matrix.mulVec_diagonal] <;> field_simp

private theorem compl_XY (h2 : (2 : k) ≠ 0) (α β : kˣ) :
    IsCompl (LinearMap.range (pX α β)) (LinearMap.range (pY (k := k))) := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    have h2' := congrFun hb 2
    have h3 := congrFun hb 3
    simp [pX_apply, pY_apply] at h0 h1 h2' h3
    have e1 : b 1 = 0 := mul_left_cancel₀ h2 (by linear_combination h0 + h2')
    have e0 : b 0 = 0 := mul_left_cancel₀ h2 (by linear_combination h3 - h1)
    rw [← hb]
    ext i; fin_cases i <;> simp [pY_apply, e0, e1]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨_, ⟨![α * (v 1 + v 3) / 2, β * (v 0 - v 2) / 2], rfl⟩, _,
      ⟨![(v 3 - v 1) / 2, (v 0 + v 2) / 2], rfl⟩, ?_⟩
    ext i; fin_cases i <;> simp [pX_apply, pY_apply] <;> field_simp <;> ring

private theorem gl_surj (g : GL (Fin 2) k) (b : Fin 2 → k) : ∃ a, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ a = b :=
  ⟨((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ b, by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

end

theorem UpperTheory.mix_invariant_plane_decomposition :
    UpperTheory.V.Sd.S2.MixIrr := by
  intro k Γ₀ Γ _ _ _ j t α β ρ R hm U hU hirr hne
  have hi := hm.index
  have hcj : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := by
    intro h
    have : t⁻¹ * j h * t ∈ j.range := by
      rw [mul_assoc]
      simp only [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff, hm.nmem]
      simp
    exact this
  have hX : ∀ h a, (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a = pX α β ((ρ h : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro h a
    obtain ⟨h', e⟩ := hcj h
    rw [hm.on h h' e, mix_pX hm.two]
  have hY : ∀ h h', j h' = t⁻¹ * j h * t → ∀ a,
      (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pY a = pY ((ρ h' : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro h h' e a
    rw [hm.on h h' e, mix_pY hm.two]
  obtain ⟨s, hsU, hs⟩ := SetLike.not_le_iff_exists.1 hU
  obtain ⟨h₀, hh₀⟩ : s * t⁻¹ ∈ j.range := by
    simp only [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff, hm.nmem, hs]
  obtain ⟨h₀', e₀⟩ := hcj h₀
  have hsX : ∀ a, (R s : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a = pY ((ρ h₀' : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro a
    have : s = j h₀ * t := by rw [hh₀]; group
    rw [this, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hm.off, diag_pX, hY h₀ h₀' e₀]
  have hmap : (LinearMap.range (pX α β)).map (matRep (R.comp U.subtype) ⟨s, hsU⟩) = LinearMap.range (pY (k := k)) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, (hsX a).symm⟩
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := gl_surj (ρ h₀') b
      exact ⟨_, ⟨a, rfl⟩, hsX a⟩
  have key := mackeyTwo (matRep (R.comp U.subtype)) (j.range.subgroupOf U) ⟨s, hsU⟩ (LinearMap.range (pX α β))
    ?_ hs ?_ ?_ ?_ ?_
  · refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => key W fun g _ v hv => hW g v hv⟩
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsU⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mul_mem_iff_of_index_two hi, hs]
    by_cases hb : (b : Γ) ∈ j.range <;> simp [hb]
  · rintro ⟨g, hg⟩ ⟨h, rfl : j h = g⟩ _ ⟨a, rfl⟩
    exact ⟨_, (hX h a).symm⟩
  · intro W hle hW
    rcases hirr.2.2 (W.comap (pX α β)) le_top (by
      rintro ⟨h, hh⟩ a ha
      have := hW ⟨j h, hh⟩ ⟨h, rfl⟩ _ ha
      change (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a ∈ W at this
      rw [hX] at this
      exact this) with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨a, rfl⟩ := hle hw
      have : a ∈ W.comap (pX α β) := hw
      rw [h0, Submodule.mem_bot] at this
      simp [this]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨a, rfl⟩
      have : a ∈ W.comap (pX α β) := by rw [h0]; trivial
      exact this
  · rw [hmap]; exact compl_XY hm.two α β
  · rw [hmap]
    rintro ⟨e, he⟩
    let f : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) :=
      (LinearEquiv.ofInjective _ (pX_inj α β)).trans (e.trans (LinearEquiv.ofInjective _ pY_inj).symm)
    have hf : ∀ a, pY (f a) = e ⟨pX α β a, a, rfl⟩ := by
      intro a
      have := congrArg Subtype.val ((LinearEquiv.ofInjective _ (pY_inj (k := k))).apply_symm_apply (e ⟨pX α β a, a, rfl⟩))
      exact this
    let M : GL (Fin 2) k :=
      ⟨LinearMap.toMatrix' (f : (Fin 2 → k) →ₗ[k] (Fin 2 → k)), LinearMap.toMatrix' (f.symm : (Fin 2 → k) →ₗ[k] (Fin 2 → k)),
        by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
    have hM : ∀ a, (M : Matrix (Fin 2) (Fin 2) k) *ᵥ a = f a := by
      intro a
      simp [M, LinearMap.toMatrix'_mulVec]
    refine hne ⟨M, fun h h' hh e' => ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro a
    simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hM]
    apply pY_inj
    rw [← hY h h' e', hf, hf]
    exact (he ⟨j h, hh⟩ ⟨h, rfl⟩ ⟨pX α β a, a, rfl⟩ ⟨_, _, rfl⟩ (hX h a).symm).symm
