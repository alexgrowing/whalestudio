import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverageStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Prod

variable {G₁ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
  {G₂ : Type} [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]

theorem isCoLat_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂) :
    IsCoLat (Γ₁.prod Γ₂) := by
  obtain ⟨d₁, K₁, hK₁, c₁⟩ := h₁
  obtain ⟨d₂, K₂, hK₂, c₂⟩ := h₂
  refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun z => ?_⟩
  · refine DiscreteTopology.of_continuous_injective
      (f := fun z : Γ₁.prod Γ₂ => ((⟨z.1.1, (AddSubgroup.mem_prod.1 z.2).1⟩ : Γ₁),
        (⟨z.1.2, (AddSubgroup.mem_prod.1 z.2).2⟩ : Γ₂))) ?_ ?_
    · exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    · intro a b h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  · obtain ⟨γ₁, hγ₁, e₁⟩ := c₁ z.1
    obtain ⟨γ₂, hγ₂, e₂⟩ := c₂ z.2
    exact ⟨(γ₁, γ₂), AddSubgroup.mem_prod.2 ⟨hγ₁, hγ₂⟩, ⟨e₁, e₂⟩⟩

end Prod

section FD

open Pointwise

variable {G₁ : Type} [AddCommGroup G₁] [MeasurableSpace G₁]
  {G₂ : Type} [AddCommGroup G₂] [MeasurableSpace G₂]

theorem vadd_prod_set {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (g : Γ₁.prod Γ₂) (A : Set G₁) (B : Set G₂) :
    g +ᵥ (A ×ˢ B) = ((g : G₁ × G₂).1 +ᵥ A) ×ˢ ((g : G₁ × G₂).2 +ᵥ B) := by
  ext ⟨x, y⟩
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
  rfl

theorem isAddFundamentalDomain_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} {μ₁ : Measure G₁} {μ₂ : Measure G₂}
    [SFinite μ₁] [SFinite μ₂] {𝓕₁ : Set G₁} {𝓕₂ : Set G₂}
    (h₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ₁) (h₂ : IsAddFundamentalDomain Γ₂ 𝓕₂ μ₂) :
    IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) where
  nullMeasurableSet := h₁.nullMeasurableSet.prod h₂.nullMeasurableSet
  ae_covers := by
    have a₁ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₁, γ +ᵥ z.1 ∈ 𝓕₁ := Measure.quasiMeasurePreserving_fst.ae h₁.ae_covers
    have a₂ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₂, γ +ᵥ z.2 ∈ 𝓕₂ := Measure.quasiMeasurePreserving_snd.ae h₂.ae_covers
    filter_upwards [a₁, a₂] with z ⟨γ₁, e₁⟩ ⟨γ₂, e₂⟩
    exact ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), AddSubgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨e₁, e₂⟩⟩
  aedisjoint := by
    intro g g' hne
    change μ₁.prod μ₂ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₂)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₂))) = 0
    rw [vadd_prod_set, vadd_prod_set, Set.prod_inter_prod, Measure.prod_prod]
    by_cases e : (g : G₁ × G₂).1 = (g' : G₁ × G₂).1
    · have e2 : (g : G₁ × G₂).2 ≠ (g' : G₁ × G₂).2 := fun e2 => hne (Subtype.ext (Prod.ext e e2))
      have := h₂.aedisjoint (i := ⟨(g : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g.2).2⟩)
        (j := ⟨(g' : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g'.2).2⟩) (fun h => e2 (congrArg Subtype.val h))
      rw [show μ₂ (((g : G₁ × G₂).2 +ᵥ 𝓕₂) ∩ ((g' : G₁ × G₂).2 +ᵥ 𝓕₂)) = 0 from this, mul_zero]
    · have := h₁.aedisjoint (i := ⟨(g : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g.2).1⟩)
        (j := ⟨(g' : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g'.2).1⟩) (fun h => e (congrArg Subtype.val h))
      rw [show μ₁ (((g : G₁ × G₂).1 +ᵥ 𝓕₁) ∩ ((g' : G₁ × G₂).1 +ᵥ 𝓕₁)) = 0 from this, zero_mul]

end FD

section Main

theorem avg_prod (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
    (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]
    (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂) (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  letI m₁ : MeasurableSpace G₁ := borel G₁
  haveI : BorelSpace G₁ := ⟨rfl⟩
  letI m₂ : MeasurableSpace G₂ := borel G₂
  haveI : BorelSpace G₂ := ⟨rfl⟩
  have e₁ : ∃ p : Measure G₁ × Set G₁, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₁ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₁ Γ₁ h₁
    exact ⟨(μ, F), a, b, c⟩
  have e₂ : ∃ p : Measure G₂ × Set G₂, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₂ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₂ Γ₂ h₂
    exact ⟨(μ, F), a, b, c⟩
  have A₁ : ∀ Ψ : G₁ → ℂ, avg Γ₁ Ψ = ∫ x in e₁.choose.2, Ψ x ∂e₁.choose.1 := fun Ψ => dif_pos e₁
  have A₂ : ∀ Ψ : G₂ → ℂ, avg Γ₂ Ψ = ∫ y in e₂.choose.2, Ψ y ∂e₂.choose.1 := fun Ψ => dif_pos e₂
  obtain ⟨H₁, F₁, M₁⟩ := e₁.choose_spec
  obtain ⟨H₂, F₂, M₂⟩ := e₂.choose_spec
  set μ₁ := e₁.choose.1
  set 𝓕₁ := e₁.choose.2
  set μ₂ := e₂.choose.1
  set 𝓕₂ := e₂.choose.2
  have hFD : IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := isAddFundamentalDomain_prod F₁ F₂
  have hM : μ₁.prod μ₂ (𝓕₁ ×ˢ 𝓕₂) = 1 := by rw [Measure.prod_prod, M₁, M₂, one_mul]
  obtain ⟨-, -, hI, hE⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (G₁ × G₂) (Γ₁.prod Γ₂) (isCoLat_prod h₁ h₂) (μ₁.prod μ₂) (𝓕₁ ×ˢ 𝓕₂)
    inferInstance hFD Φ hΦ
  rw [hM, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hE
  rw [← hE, setIntegral_prod _ hI, A₁]
  simp only [A₂]

end Main

end GlobalTheory.CuspGeneric
