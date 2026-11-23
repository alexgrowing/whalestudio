import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_of_iso {k : Type} [CommRing k] {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k) (e : X' ≅ X)
    (he : e.hom ≫ s = s') (hW : WedgeO (OAff s)) : WedgeO (OAff s') := by
  have h1 : e.hom ≫ s = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, he]
  have h2 : e.inv ≫ s' = s ≫ spMap (RingHom.id k) := by
    rw [spMap_id, Category.comp_id, ← he, Iso.inv_hom_id_assoc]
  have hid : (𝟙 X) ≫ s = s ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have hid' : (𝟙 X') ≫ s' = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have P := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  have c1 := (P.1 k k X X' s s' (RingHom.id k) e.hom h1 k X s (RingHom.id k) e.inv h2 (RingHom.id k) (𝟙 X) hid
    (by simp) (fun _ ↦ rfl))
  have c2 := (P.1 k k X' X s' s (RingHom.id k) e.inv h2 k X' s' (RingHom.id k) e.hom h1 (RingHom.id k) (𝟙 X') hid'
    (by simp) (fun _ ↦ rfl))
  have i1 := P.2.2 k (Over.mk s)
  have i2 := P.2.2 k (Over.mk s')
  have hcup := (P.2.1 k k X X' s s' (RingHom.id k) e.hom h1).1

  let f1 : HO1 s →ₗ[k] HO1 s' := pullHO1 h1
  let g1 : HO1 s' →ₗ[k] HO1 s := pullHO1 h2
  let f2 : HO2 s →ₗ[k] HO2 s' := pullHO2 h1
  let g2 : HO2 s' →ₗ[k] HO2 s := pullHO2 h2
  have fg1 : ∀ a, f1 (g1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c2.1]; exact i2.1 a
  have gf1 : ∀ a, g1 (f1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c1.1]; exact i1.1 a
  have fg2 : ∀ a, f2 (g2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c2.2.1]; exact i2.2.1 a
  have gf2 : ∀ a, g2 (f2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c1.2.1]; exact i1.2.1 a
  let e2 : HO2 s ≃ₗ[k] HO2 s' := LinearEquiv.ofLinear f2 g2 (LinearMap.ext fg2) (LinearMap.ext gf2)
  let eΛ : ⋀[k]^2 (HO1 s') ≃ₗ[k] ⋀[k]^2 (HO1 s) :=
    LinearEquiv.ofLinear (exteriorPower.map 2 g1) (exteriorPower.map 2 f1)
      (by rw [← exteriorPower.map_comp, show g1 ∘ₗ f1 = LinearMap.id from LinearMap.ext gf1,
        exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, show f1 ∘ₗ g1 = LinearMap.id from LinearMap.ext fg1,
        exteriorPower.map_id])
  obtain ⟨E, hE⟩ := hW
  refine ⟨(eΛ.trans E).trans e2, fun a b ↦ ?_⟩
  have hm : (⇑g1 ∘ ![a, b]) = ![g1 a, g1 b] := by
    ext i; fin_cases i <;> rfl
  change f2 (E (exteriorPower.map 2 g1 (exteriorPower.ιMulti k 2 ![a, b]))) = _
  rw [exteriorPower.map_apply_ιMulti, hm, hE]
  simp only [f2]
  rw [hcup]
  rw [show pullHO1 h1 (g1 a) = a from fg1 a, show pullHO1 h1 (g1 b) = b from fg1 b]

end GlobalTheory.AbCohWedgeLift

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_fibre : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  intro hF R _ A _ g hA hg k _ σ X₀ s₀ ψ w
  letI : Algebra R k := σ.toAlgebra
  obtain ⟨B, _, pr, -, hB, hBg, hsq, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R k A g hA hg
  have hsq' : IsPullback pr B.hom A.hom (spMap σ) := hsq
  have hW : WedgeO (OAff B.hom) := (hF k (Field.toIsField k) B g hB hBg).2.2
  let e : X₀ ≅ B.left := IsPullback.isoIsPullback _ _ w hsq'
  exact wedgeO_of_iso B.hom s₀ e (IsPullback.isoIsPullback_hom_snd _ _ w hsq') hW

end GlobalTheory.AbCohWedgeLift
