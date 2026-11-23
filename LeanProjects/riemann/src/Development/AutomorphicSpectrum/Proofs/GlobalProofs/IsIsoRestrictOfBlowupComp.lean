import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Principalise

theorem isIso_of_isIso_comp_of_dense_range {A P V : Scheme.{0}} (a : A ⟶ P) (b : P ⟶ V) [IsIso (a ≫ b)]
    [IsSeparated b] [IsReduced P] (hd : Dense (Set.range a)) : IsIso b ∧ IsIso a := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : V ⟶ P, σ = inv (a ≫ b) ≫ a := ⟨_, rfl⟩
  have hσ : σ ≫ b = 𝟙 V := by simp [hσdef]
  have haσ : (a ≫ b) ≫ σ = a := by simp [hσdef]
  have hid : IsIso (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ b
  have hr : Set.range a ⊆ Set.range σ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(a ≫ b) x, by rw [← Scheme.Hom.comp_apply, haσ]⟩
  have hcl : IsClosed (Set.range σ) := σ.isClosedEmbedding.isClosed_range
  have : Surjective σ := ⟨Set.range_eq_univ.1 (by
    have h := (hd.mono hr).closure_eq
    rwa [hcl.closure_eq] at h)⟩
  have : IsIso σ := isIso_of_isClosedImmersion_of_surjective σ
  have hb : IsIso b := IsIso.of_isIso_comp_left σ b
  exact ⟨hb, IsIso.of_isIso_comp_right a b⟩

theorem isEmpty_of_effCartier_bot {W : Scheme.{0}} (h : FinalTheorems.EffCartier (⊥ : W.IdealSheafData)) : IsEmpty W := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, f, hx, hf, e⟩ := h x
  have hf0 : f = 0 := by
    have : f ∈ (⊥ : W.IdealSheafData).ideal U := e ▸ Ideal.mem_span_singleton_self f
    simpa using this
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  exact nonZeroDivisors.ne_zero hf hf0

theorem dense_range_restrict_of_blowup {X₁ X₂ : Scheme.{0}} [IsIntegral X₁] [Nonempty X₂] {π : X₂ ⟶ X₁}
    {Z : X₁.IdealSheafData} (hB : FinalTheorems.Blowup π Z) (U : X₁.Opens) : Dense (Set.range (π ∣_ U)) := by
  have hZ : Z ≠ ⊥ := by
    rintro rfl
    have h := hB.1
    rw [Scheme.IdealSheafData.comap_bot] at h
    exact (isEmpty_of_effCartier_bot h).false (Nonempty.some inferInstance)
  have hO := GlobalTheory.Principalise.nonempty_compl_support hZ
  have hiso : IsIso (π ∣_ Z.support.compl) :=
    GlobalTheory.Principalise.isIso_restrict_of_blowup hB _ fun x hx => hx
  have hdO : Dense (Z.support.compl : Set X₁) := Z.support.compl.isOpen.dense hO
  have hdU : Dense (U.ι ⁻¹' (Z.support.compl : Set X₁)) := hdO.preimage U.ι.isOpenMap
  refine hdU.mono fun x hx => ?_
  obtain ⟨y, hy⟩ := (π ∣_ Z.support.compl).surjective ⟨x.1, hx⟩
  have hw : π y.1 = x.1 := by
    have := morphismRestrict_base_coe π Z.support.compl y
    rw [hy] at this
    exact this.symm
  refine ⟨⟨y.1, show π y.1 ∈ U by rw [hw]; exact x.2⟩, Subtype.ext ?_⟩
  exact (morphismRestrict_base_coe π U ⟨y.1, _⟩).trans hw

theorem isIso_restrict_of_isIso_restrict_comp_blowup : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁)
    (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ →
    IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  intro X X₁ X₂ s π Z V hX hs hB hne he
  have he' : IsIso (π ∣_ (s ⁻¹ᵁ V) ≫ s ∣_ V) := by
    rw [← morphismRestrict_comp]
    exact he
  exact isIso_of_isIso_comp_of_dense_range (π ∣_ (s ⁻¹ᵁ V)) (s ∣_ V) (dense_range_restrict_of_blowup hB _)

end GlobalTheory.CompanionTheory.Principalise
