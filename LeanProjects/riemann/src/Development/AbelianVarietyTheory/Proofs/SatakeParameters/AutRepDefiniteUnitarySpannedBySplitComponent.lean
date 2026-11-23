import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorpStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong

theorem locU_conj_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (y : UA E a) {x : UA E a} (hx : x ∈ locU a w) : y * x * y⁻¹ ∈ locU a w := by
  simp only [locU, finU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, map_mul, map_inv] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  exact ⟨by simp [h1], fun u hu => by simp [h2 u hu]⟩

theorem exists_locU_mul_comm {E : Type} [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (hw : IsSplitAt w) (g : UA E a) :
    ∃ x ∈ locU a w, ∃ y : UA E a, g = x * y ∧ ∀ z ∈ locU a w, y * z = z * y := by
  have hb := (GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw).1
  obtain ⟨x, hx⟩ := hb.2 (cLoc w g)
  have hx' : cLoc w (x : UA E a) = cLoc w g := hx
  refine ⟨x, x.2, (x : UA E a)⁻¹ * g, by group, fun z hz => ?_⟩
  have hy : cLoc w ((x : UA E a)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
  have hc := locU_conj_mem w ((x : UA E a)⁻¹ * g) hz
  have he : (⟨_, hc⟩ : locU a w) = ⟨z, hz⟩ := hb.1 (by
    change cLoc w (_ * z * _) = cLoc w z
    rw [map_mul, map_mul, map_inv, hy]; group)
  have he' := congrArg Subtype.val he
  simp only at he'
  calc (x : UA E a)⁻¹ * g * z = ((x : UA E a)⁻¹ * g * z * ((x : UA E a)⁻¹ * g)⁻¹) * ((x : UA E a)⁻¹ * g) := by group
    _ = z * ((x : UA E a)⁻¹ * g) := by rw [he']

theorem span_comp_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  intro E _ _ _ a U hU w hw σ hσ φ hφ
  set S := ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
    f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 with hS
  have hSU : S ≤ U := iSup_le fun f => by
    rintro _ ⟨v, rfl⟩; exact f.2.1 v
  obtain ⟨-, f0, hf0, hf0U, hf0e⟩ := hσ
  have hS0 : S ≠ ⊥ := by
    intro h
    apply hf0
    ext v
    have : f0 v ∈ S := (le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
      f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) ⟨f0, hf0U, hf0e⟩) ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at this
    simp [this]

  have hloc : ∀ x : locU a w, ∀ ψ ∈ S, RU E a x ψ ∈ S := by
    intro x ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a x ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      rw [← f.2.2 x v]
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f ⟨_, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; rw [map_add]; exact add_mem h₁ h₂

  have hcen : ∀ y : UA E a, (∀ z ∈ locU a w, y * z = z * y) → ∀ ψ ∈ S, RU E a y ψ ∈ S := by
    intro y hy ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a y ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      let f' : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
          f (σ.ρ (cLoc w x) v) = RU E a x (f v)} :=
        ⟨RU E a y ∘ₗ f.1, fun v => hU.stable y _ (f.2.1 v), fun x v => by
          simp only [LinearMap.comp_apply]
          rw [f.2.2 x v, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hy x x.2]⟩
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f' ⟨v, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; rw [map_add]; exact add_mem h₁ h₂
  have hstab : ∀ g, ∀ ψ ∈ S, RU E a g ψ ∈ S := by
    intro g ψ hψ
    obtain ⟨x, hx, y, rfl, hy⟩ := exists_locU_mul_comm a w hw g
    rw [map_mul, Module.End.mul_apply]
    exact hloc ⟨x, hx⟩ _ (hcen y hy ψ hψ)
  rcases hU.irred S hSU hstab with h | h
  · exact absurd h hS0
  · rw [h]; exact hφ

end GlobalTheory.Cong
