import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma twisted_kernel_forms_nonvanishing (hE : EtDesc) (k : Type) [Field k] [IsAlgClosed k] (A A₁ A₂ : Over (Sp k)) [GrpObj A]
    [GrpObj A₁] [GrpObj A₂] (hA : IsAbelianScheme A) (hA₂ : IsAbelianScheme A₂)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left]
    (hker : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp k) (a : Over.mk t ⟶ A), a ≫ ψ₁ = 1 → a ≫ ψ₂ = 1) :
    ∃ θ : A₁ ⟶ A₂, ψ₁ ≫ θ = ψ₂ := by
  haveI := hA.smooth
  haveI := hA₂.proper
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : ψ₂.left ≫ A₂.hom = ψ₁.left ≫ A₁.hom := by rw [Over.w, Over.w]
  obtain ⟨hepi, g, hg⟩ := hE ψ₁.left A₁.hom A₂.hom ψ₂.left hw (by
    intro Ω _ _ x y hxy
    have hxy' : x ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ₁, ← Category.assoc, hxy, Category.assoc]
    let X : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk x
    let Y : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk y hxy'.symm
    have h1 : X ≫ ψ₁ = Y ≫ ψ₁ := Over.OverMorphism.ext hxy
    have h2 : (X * Y⁻¹) ≫ ψ₁ = 1 := by
      have e := (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
      have e' := map_inv (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))) Y
      simp only [IsMonHom.monoidHom_apply] at e e'
      rw [e, e', h1, mul_inv_cancel]
    have h3 := hker Ω (x ≫ A.hom) (X * Y⁻¹) h2
    have e := (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
    have e' := map_inv (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))) Y
    simp only [IsMonHom.monoidHom_apply] at e e'
    rw [e, e', mul_inv_eq_one] at h3
    exact congrArg CommaMorphism.left h3)
  haveI := hepi
  refine ⟨Over.homMk g ?_, ?_⟩
  · rw [← cancel_epi ψ₁.left, ← Category.assoc, hg, hw]
  · exact Over.OverMorphism.ext hg

theorem UpperTheory.Gal.G3.pQuotUniq :
    EtDesc → QuotUniq := by
  intro hE k _ _ A A₁ A₂ _ _ _ _ _ _ hA hA₁ hA₂ ψ₁ ψ₂ h₁ h₂ f₁ e₁ s₁ f₂ e₂ s₂ hker
  obtain ⟨θ, hθ⟩ := twisted_kernel_forms_nonvanishing hE k A A₁ A₂ hA hA₂ ψ₁ ψ₂ (fun Ω _ _ t a => (hker Ω t a).1)
  obtain ⟨θ', hθ'⟩ := twisted_kernel_forms_nonvanishing hE k A A₂ A₁ hA hA₁ ψ₂ ψ₁ (fun Ω _ _ t a => (hker Ω t a).2)
  haveI : Flat ψ₁.left := inferInstance
  haveI : Flat ψ₂.left := inferInstance
  haveI : Epi ψ₁ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₁
  haveI : Epi ψ₂ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₂
  haveI : Epi (ψ₁ ⊗ₘ ψ₁) := GlobalTheory.FlatQuotient.epi_tensorHom ψ₁ ψ₁
  have i1 : θ ≫ θ' = 𝟙 _ := by
    rw [← cancel_epi ψ₁, ← Category.assoc, hθ, hθ', Category.comp_id]
  have i2 : θ' ≫ θ = 𝟙 _ := by
    rw [← cancel_epi ψ₂, ← Category.assoc, hθ', hθ, Category.comp_id]
  refine ⟨θ, ⟨θ', i1, i2⟩, ⟨?_, ?_⟩, hθ⟩
  · rw [← IsMonHom.one_hom ψ₁, Category.assoc, hθ, IsMonHom.one_hom ψ₂]
  · have h1 : (ψ₁ ⊗ₘ ψ₁) ≫ (θ ⊗ₘ θ) = ψ₂ ⊗ₘ ψ₂ := by
      rw [tensorHom_comp_tensorHom, hθ]
    rw [← cancel_epi (ψ₁ ⊗ₘ ψ₁), ← Category.assoc, ← IsMonHom.mul_hom ψ₁, Category.assoc, hθ,
      IsMonHom.mul_hom ψ₂, ← Category.assoc, h1]
