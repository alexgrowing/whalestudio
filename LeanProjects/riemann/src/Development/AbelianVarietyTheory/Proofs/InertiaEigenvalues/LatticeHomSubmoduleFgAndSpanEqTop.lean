import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdEApply
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.StableLatCount

theorem exists_smul_mem_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E] [Algebra O E]
    [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (a : A) :
    ∃ d ∈ nonZeroDivisors O, d • a ∈ M := by
  have ha : a ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₂ * d₁, mul_mem hd₂ hd₁, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm d₂ d₁ y]
    exact M.add_mem (M.smul_mem _ h₁) (M.smul_mem _ h₂)
  | smul e x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨o, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have h1 : (s : O) • (e • x) = o • x := by
      rw [← algebraMap_smul E (s : O) (e • x), smul_smul, mul_comm, hs, algebraMap_smul]
    refine ⟨(s : O) * d, mul_mem s.2 hd, ?_⟩
    rw [mul_comm, mul_smul, h1, smul_comm d o x]
    exact M.smul_mem o h

theorem exists_smul_mem_finset_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E]
    [Algebra O E] [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A]
    [IsScalarTower O E A] (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (t : Finset A) :
    ∃ d ∈ nonZeroDivisors O, ∀ a ∈ t, d • a ∈ M := by
  classical
  refine Finset.induction_on t ⟨1, one_mem _, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨d₁, hd₁, h₁⟩ := ih
  obtain ⟨d₂, hd₂, h₂⟩ := exists_smul_mem_of_span_eq_top O E M hM a
  refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, ?_⟩
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [mul_smul]; exact M.smul_mem _ h₂
  · rw [mul_comm, mul_smul]; exact M.smul_mem _ (h₁ b hb)

theorem homLat_fg_and_span_eq_top (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁]
    [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂]
    [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) :
    IsLat O E M₁ → IsLat O E M₂ →
      (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  classical
  intro h₁ h₂
  obtain ⟨h₁fg, h₁sp⟩ := h₁
  obtain ⟨h₂fg, h₂sp⟩ := h₂
  obtain ⟨s, hs⟩ := h₂fg
  have hsE : Submodule.span E (s : Set A₂) = ⊤ := by
    rw [eq_top_iff, ← h₂sp, Submodule.span_le, ← hs]
    exact fun x hx => Submodule.span_le_restrictScalars O E _ hx
  have memH : ∀ ψ ∈ homLat E M₁ M₂, ∀ x ∈ M₂, ψ x ∈ M₁ := fun ψ hψ => hψ
  refine ⟨?_, ?_⟩
  · haveI : Module.Finite O M₁ := Module.Finite.iff_fg.mpr h₁fg
    let f : homLat E M₁ M₂ →ₗ[O] (s → M₁) :=
      { toFun := fun ψ x => ⟨ψ.1 x, memH ψ.1 ψ.2 x (hs ▸ Submodule.subset_span x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro ψ φ h
      apply Subtype.ext
      apply LinearMap.ext_on hsE
      intro x hx
      exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
    haveI := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.mp this
  · rw [eq_top_iff]
    intro ψ _
    obtain ⟨d, hd, hdψ⟩ := exists_smul_mem_finset_of_span_eq_top O E M₁ h₁sp (s.image ψ)
    have hmem : d • ψ ∈ homLat E M₁ M₂ := by
      show ∀ x ∈ M₂, (d • ψ) x ∈ M₁
      intro x hx
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => rw [LinearMap.smul_apply]; exact hdψ _ (Finset.mem_image_of_mem _ hy)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact M₁.add_mem hy hz
      | smul o y _ hy => rw [LinearMap.map_smul_of_tower]; exact M₁.smul_mem o hy
    have hd' : algebraMap O E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hψ : ψ = (algebraMap O E d)⁻¹ • (d • ψ) := by
      rw [← algebraMap_smul E d ψ, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.StableLatCount
