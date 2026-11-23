import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianSStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHodgeFiltrationFunctionalExtendsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieHodge

theorem lieExact_of_crystallineLift_hodgeDeRham : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LieExact A := by
  intro hC hH R _ A _ g hab hdim
  have hP : AllPrim (dp0 R) (𝟙 _) A :=
    (GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison hC hH) R A g hab hdim).1
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp : Function.Injective (GlobalTheory.CechDR.cmp1 (A.hom ≫ 𝟙 (Sp R))) :=
    (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1.1
  have hcl : Function.Injective (GlobalTheory.CechDR.clForm (A.hom ≫ 𝟙 (Sp R))) :=
    (hH R A g hab hdim).2.2.2.2.1.2.1
  have hcf : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)),
      Form.cl _ f = 0 ↔ GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 := fun f ↦
    ⟨fun h ↦ hcl (by rw [← GlobalTheory.CechDR.comparison_formClass, h, map_zero, map_zero]),
      fun h ↦ hcmp (by rw [GlobalTheory.CechDR.comparison_formClass, h, map_zero, map_zero])⟩
  have hmem : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f ∈ primDR A := fun f ↦ by
    have : primDR A = ⊤ := hP
    rw [this]; exact Submodule.mem_top
  let F : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] primDR A := (Form.cl _).codRestrict _ hmem
  refine ⟨fun h ↦ ?_, fun v hv ↦ ?_⟩
  · obtain ⟨v, hv, hvf⟩ := GlobalTheory.T.exists_tangentVector_functional_globalForms_abelianScheme hC hH R A g hab hdim (h ∘ₗ F) (fun f hf ↦ by
      have e : F f = 0 := Subtype.ext ((hcf f).2 hf)
      rw [LinearMap.comp_apply, e, map_zero])
    refine ⟨v, ⟨hv, fun f hf ↦ (hvf f).symm⟩, fun w hw ↦ GlobalTheory.T.abelianScheme_tangent_eq_of_crystallineValues_eq hC hH R A g hab hdim w v hw.1 hv
      fun f ↦ ((hw.2 f (hmem f)).symm.trans (hvf f).symm)⟩
  · have hfac : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f = 0 → tanVal v f = 0 :=
      fun f h0 ↦ GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero R A v f ((hcf f).1 h0)
    have hF1 : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := fun f ↦ by
      rw [hodgeFiltration_eq_range]; exact ⟨f, rfl⟩
    let c1 : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] F1 (A.hom ≫ 𝟙 (Sp R)) := (Form.cl _).codRestrict _ hF1
    have hc1 : Function.Surjective c1 := by
      rintro ⟨c, hc⟩
      rw [hodgeFiltration_eq_range] at hc
      obtain ⟨f, rfl⟩ := hc
      exact ⟨f, rfl⟩
    let e := c1.quotKerEquivOfSurjective hc1
    have hker : LinearMap.ker c1 ≤ LinearMap.ker (tanVal v) :=
      fun f hf ↦ hfac f (congrArg Subtype.val hf)
    let ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R :=
      (LinearMap.ker c1).liftQ (tanVal v) hker ∘ₗ e.symm.toLinearMap
    have hψ : ∀ f, ψ (c1 f) = tanVal v f := fun f ↦ by
      have : e.symm (c1 f) = Submodule.Quotient.mk f := e.symm_apply_eq.2 rfl
      change (LinearMap.ker c1).liftQ (tanVal v) hker (e.symm (c1 f)) = _
      rw [this]; rfl
    obtain ⟨H, hH'⟩ := GlobalTheory.T.abelianScheme_hodgeFiltration_functional_extends hC hH R A g hab hdim ψ
    exact ⟨H ∘ₗ (primDR A).subtype, hv, fun f hf ↦ (hH' (c1 f)).trans (hψ f)⟩

end GlobalTheory.LieHodge
