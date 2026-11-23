import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

theorem coef_span_finset {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ s : Finset (PadicAlgCl l), (∀ x ∈ s, IsIntegral ℤ_[l] x) ∧
      ∀ x ∈ c.O, x ∈ Submodule.span ℤ_[l] (s : Set (PadicAlgCl l)) := by
  classical
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] c.O).FG)
  refine ⟨t.image (↑), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c.O.val
  · intro x hx
    have hy : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (t : Set c.O) := ht ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := c.O.val.toLinearMap) hy
    rw [Submodule.map_span] at h2
    simpa [Finset.coe_image] using h2

theorem coef_common (l : ℕ) [Fact l.Prime] (c₁ c₂ : Coef l) :
    ∃ c₃ : Coef l, c₁.O ≤ c₃.O ∧ c₂.O ≤ c₃.O := by
  classical
  obtain ⟨s₁, hs₁, h₁⟩ := coef_span_finset c₁
  obtain ⟨s₂, hs₂, h₂⟩ := coef_span_finset c₂
  let S : Set (PadicAlgCl l) := ((s₁ ∪ s₂ : Finset _) : Set _)
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] S
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  let c₃ : Coef l := ⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩
  have key : ∀ (c : Coef l) (s : Finset (PadicAlgCl l)), (s : Set (PadicAlgCl l)) ⊆ S →
      (∀ x ∈ c.O, x ∈ Submodule.span ℤ_[l] (s : Set (PadicAlgCl l))) → c.O ≤ c₃.O := by
    intro c s hsS hc x hx
    have hspan : Submodule.span ℤ_[l] (s : Set (PadicAlgCl l)) ≤
        (K.toSubalgebra.restrictScalars ℤ_[l]).toSubmodule := by
      rw [Submodule.span_le]
      intro y hy
      exact IntermediateField.subset_adjoin ℚ_[l] S (hsS hy)
    have hxK : x ∈ K := hspan (hc x hx)
    have hxi : IsIntegral ℤ_[l] x :=
      (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
    exact ⟨⟨x, hxK⟩, (isIntegral_algHom_iff f hf).1 hxi, rfl⟩
  exact ⟨c₃, key c₁ s₁ (by simp [S]) h₁, key c₂ s₂ (by simp [S]) h₂⟩

end GlobalTheory
