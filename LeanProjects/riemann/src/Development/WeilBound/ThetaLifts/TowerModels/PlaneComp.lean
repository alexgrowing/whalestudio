import Development.WeilBound.ThetaLifts.TowerModels.PlaneForm

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_compl (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (hn : n = n₁ + 2)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) (hyx : form σ J y x ≠ 0) :
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  let f : (Fin n → E) →ₗ[E] E × E := (formL (σ := σ) J x).prod (formL (σ := σ) J y)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨(a / form σ J y x) • y + b • x, Prod.ext ?_ ?_⟩
    · change form σ J _ x = a
      rw [form_add_left, form_smul_left, form_smul_left, hxx, div_mul_cancel₀ _ hyx, mul_zero, add_zero]
    · change form σ J _ y = b
      rw [form_add_left, form_smul_left, form_smul_left, hyy, hxy, mul_zero, mul_one, zero_add]
  have hk : Module.finrank E (LinearMap.ker f) = n₁ := by
    have := f.finrank_range_add_finrank_ker
    rw [hf, finrank_top] at this
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker f) hk
  let g : (Fin n₁ → E) →ₗ[E] (Fin n → E) := (LinearMap.ker f).subtype ∘ₗ b.equivFun.symm.toLinearMap
  obtain ⟨p, hp⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2
    ((LinearMap.ker f).injective_subtype.comp b.equivFun.symm.injective))
  refine ⟨LinearMap.toMatrix' g, LinearMap.toMatrix' p, by rw [← LinearMap.toMatrix'_comp, hp, LinearMap.toMatrix'_id],
    fun u => ?_, fun z h1 h2 => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    have := (b.equivFun.symm u).2
    exact Prod.mk_eq_zero.1 this
  · refine ⟨b.equivFun ⟨z, Prod.mk_eq_zero.2 ⟨h1, h2⟩⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    change z = (b.equivFun.symm (b.equivFun _) : LinearMap.ker f)
    rw [LinearEquiv.symm_apply_apply]

theorem fg_comap {V W : Type} [AddCommGroup V] [Module (𝓞 E) V] [AddCommGroup W] [Module (𝓞 E) W]
    (f : V →ₗ[𝓞 E] W) (hf : Function.Injective f) (L : Submodule (𝓞 E) W) (hL : L.FG) : (L.comap f).FG :=
  Submodule.fg_of_fg_map_injective f hf (hL.of_le (Submodule.map_comap_le f L))

theorem isLattice_comap (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * ι = 1) (hL : L.IsLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E where
  fg := fg_comap _ (fun u u' e => by
    have := congrArg (P *ᵥ ·) (show ι *ᵥ u = ι *ᵥ u' from e)
    simpa [Matrix.mulVec_mulVec, hP] using this) L hL.fg
  span_eq_top := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E (L : Set (Fin n → E)) (ι *ᵥ u)
      (by rw [hL.span_eq_top]; trivial)
    rw [Submodule.span_eq] at ht
    have h0 : ((t : 𝓞 E) : E) ≠ 0 := by simpa using nonZeroDivisors.coe_ne_zero t
    have : u = ((t : 𝓞 E) : E)⁻¹ • (((t : 𝓞 E) : E) • u) := by rw [inv_smul_smul₀ h0]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change ι *ᵥ (((t : 𝓞 E) : E) • u) ∈ L
    rw [Matrix.mulVec_smul]
    exact ht

theorem exists_ideal (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (x : Fin n → E) (hx : x ≠ 0) :
    ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L :=
  ⟨⟨L.comap ((LinearMap.toSpanSingleton E _ x).restrictScalars (𝓞 E)), FractionalIdeal.isFractional_of_fg
    (fg_comap _ (smul_left_injective E hx) L hL.fg)⟩, fun _ => Iff.rfl⟩

end PositivityTheory.ThKG.Tow.Pln

end
