import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory

theorem restrictGlobal_appTop_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (a : Γ(X, ⊤)) :
    restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) = f.appLE V (f ⁻¹ᵁ V) le_rfl (restrictGlobal X V a) := by
  have h : f.app V (restrictGlobal X V a) = restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) :=
    ConcreteCategory.congr_hom (f.naturality (homOfLE le_top : V ⟶ ⊤).op) _
  rw [← h, Scheme.Hom.app_eq_appLE]

theorem length_sectionsOn_pullback_of_free (O : Type) [CommRing O] {X Y : Scheme.{0}}
    [Algebra O Γ(X, ⊤)] [Algebra O Γ(Y, ⊤)] (f : Y ⟶ X)
    (hO : ∀ r : O, f.appTop (algebraMap O Γ(X, ⊤) r) = algebraMap O Γ(Y, ⊤) r)
    (V : X.Opens) (n : ℕ) (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧
      Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n)
    (G : X.Modules) [G.IsQuasicoherent] :
    Module.length O (sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)) =
      n * Module.length O (sectionsOn G V) := by
  rw [Scheme.Hom.app_eq_appLE] at hfree
  letI := appLEAlgebra f (le_refl (f ⁻¹ᵁ V))
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  obtain ⟨hF, hFin, hr⟩ := hfree
  have hbc := isBaseChange_pullbackSections f G hU hV (le_refl (f ⁻¹ᵁ V))
  let b := Module.Free.chooseBasis Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let ι := Module.Free.ChooseBasisIndex Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let E : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ V) ≃ₗ[Γ(X, V)] (ι → Γ(G, V)) :=
    (hbc.equiv.restrictScalars Γ(X, V)).symm ≪≫ₗ
      TensorProduct.congr b.equivFun (LinearEquiv.refl Γ(X, V) Γ(G, V)) ≪≫ₗ
      TensorProduct.comm _ _ _ ≪≫ₗ TensorProduct.piScalarRight _ _ _ _
  let A : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃+ (ι → sectionsOn G V) :=
    (sectionsOn.toΓ _ _).trans (E.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ ↦ (sectionsOn.toΓ G V).symm))
  let Φ : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃ₗ[O]
      (ι → sectionsOn G V) :=
    A.toLinearEquiv fun r x ↦ by
      funext i
      apply (sectionsOn.toΓ G V).injective
      change sectionsOn.toΓ G V ((sectionsOn.toΓ G V).symm
          (E (sectionsOn.toΓ _ _ (r • x)) i)) =
        sectionsOn.toΓ G V (r • (sectionsOn.toΓ G V).symm (E (sectionsOn.toΓ _ _ x) i))
      rw [AddEquiv.apply_symm_apply, sectionsOn.toΓ_smul, sectionsOn.toΓ_smul,
        AddEquiv.apply_symm_apply, ← hO, restrictGlobal_appTop_eq_appLE]
      rw [← appLEModule_smul, E.map_smul]
      rfl
  rw [Φ.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases subsingleton_or_nontrivial Γ(X, V) with hA | hA
  · haveI : Subsingleton Γ(G, V) := Module.subsingleton Γ(X, V) Γ(G, V)
    haveI : Subsingleton (sectionsOn G V) := (sectionsOn.toΓ G V).toEquiv.subsingleton_congr.2 this
    rw [Module.length_eq_zero_iff.2 this, mul_zero, mul_zero]
  · rw [← hr, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
