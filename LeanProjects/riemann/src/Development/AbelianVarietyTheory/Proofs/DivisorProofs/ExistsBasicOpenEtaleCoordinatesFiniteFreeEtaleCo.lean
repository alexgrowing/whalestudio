import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

namespace GlobalTheory.CoverDeg

theorem exists_goodCover_of_coords_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  intro k _ X Y p π D δ x U₁ U₂ hU₁ hx₁ ⟨t, ht⟩ hU₂ hx₂ hV₂ he hf hfr
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU₁ hU₂ x ⟨hx₁, hx₂⟩
  have hxU : x ∈ X.basicOpen g := hfg ▸ hxf
  refine ⟨X.basicOpen g, hxU, ?_⟩
  have hUU₁ : X.basicOpen g ≤ U₁ := hfg ▸ X.basicOpen_le f
  have hUU₂ : X.basicOpen g ≤ U₂ := X.basicOpen_le g
  have hUa : IsAffineOpen (X.basicOpen g) := hU₂.basicOpen g
  have hpre : π ⁻¹ᵁ X.basicOpen g = Y.basicOpen (π.app U₂ g) := Scheme.preimage_basicOpen π g
  have hVa : IsAffineOpen (π ⁻¹ᵁ X.basicOpen g) := hpre ▸ hV₂.basicOpen _
  have hVV₂ : π ⁻¹ᵁ X.basicOpen g ≤ π ⁻¹ᵁ U₂ := fun _ h => hUU₂ h
  refine ⟨hUa, hVa, ?_, ?_⟩
  · refine ⟨fun i => resG X hUU₁ (t i), ?_⟩
    have e : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen g)) (fun i => resG X hUU₁ (t i)) =
        (resG X hUU₁).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG X hUU₁).Etale := by
      letI : Algebra Γ(X, U₁) Γ(X, X.basicOpen g) := (resG X hUU₁).toAlgebra
      haveI : IsLocalization.Away f Γ(X, X.basicOpen g) :=
        hU₁.isLocalization_of_eq_basicOpen f (homOfLE hUU₁) hfg.symm
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ ht hR
  · letI i1 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := (π.app U₂).hom.toAlgebra
    letI i2 : Algebra Γ(X, U₂) Γ(X, X.basicOpen g) := (resG X hUU₂).toAlgebra
    letI i3 : Algebra Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (resG Y hVV₂).toAlgebra
    letI i4 : Algebra Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (π.app (X.basicOpen g)).hom.toAlgebra
    letI i5 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      ((π.app (X.basicOpen g)).hom.comp (resG X hUU₂)).toAlgebra
    have hnat : (π.app (X.basicOpen g)).hom.comp (resG X hUU₂) = (resG Y hVV₂).comp (π.app U₂).hom := by
      ext a
      exact congr($(π.naturality (homOfLE hUU₂).op) a)
    haveI : IsScalarTower Γ(X, U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' hnat
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) :=
      hU₂.isLocalization_of_eq_basicOpen g (homOfLE hUU₂) rfl
    haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g))
        Γ(Y, π ⁻¹ᵁ X.basicOpen g) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      exact hV₂.isLocalization_of_eq_basicOpen (π.app U₂ g) (homOfLE hVV₂) hpre
    haveI hpo : Algebra.IsPushout Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Algebra.isPushout_of_isLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ U₂)
        Γ(Y, π ⁻¹ᵁ X.basicOpen g)
    have het : (algebraMap Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g)).Etale :=
      RingHom.Etale.isStableUnderBaseChange _ _ _ _ he
    haveI : Module.Finite Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := hf
    haveI hfin : Module.Finite Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Module.Finite.of_isLocalization Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g)
    refine ⟨het, hfin, ?_⟩
    obtain ⟨hfree, hrk⟩ := hfr
    haveI : Nontrivial Γ(X, X.basicOpen g) := (X.presheaf.germ _ x hxU).hom.domain_nontrivial
    haveI : Nontrivial Γ(X, U₂) := (X.presheaf.germ _ x hx₂).hom.domain_nontrivial
    let b := Module.Free.chooseBasis Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂)
    let b' := hpo.symm.out.basis b
    refine ⟨Module.Free.of_basis b', ?_⟩
    rw [Module.finrank_eq_card_basis b', ← hrk, Module.finrank_eq_card_basis b]

end GlobalTheory.CoverDeg
