import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechKSSmul

theorem valR_mul_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a * b) = valR x O a * valR x O b := by
  simp only [valR, dif_pos h, map_mul]

theorem valR_sub_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a - b) = valR x O a - valR x O b := by
  simp only [valR, dif_pos h, map_sub]

theorem valR_appLE_comp {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ W) (a : Γ(Z, U)) :
    valR x W ((g.appLE U W e).hom a) = valR (x ≫ g) U a := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun y hy => e (h hy)
  simp only [valR, dif_pos h, dif_pos h']
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (q.hom a))
    (Scheme.Hom.appLE_comp_appLE x g U W ⊤ e h)

theorem fromSpec_appLE_top_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem valR_spMap_chart {X : Scheme.{0}} (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (r : Γ(X, U.1)) : valR (spMap φ ≫ chart U) U.1 r = φ r := by
  have h1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := by
    show ⊤ ≤ U.2.fromSpec ⁻¹ᵁ U.1
    rw [U.2.fromSpec_preimage_self]
  rw [← valR_appLE_comp (spMap φ) (chart U) U.1 ⊤ h1 (fun _ _ => trivial)]
  have e : (chart U).appLE U.1 ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    exact fromSpec_appLE_top_eq U.2 h1
  rw [e]
  simp only [valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from fun _ _ => trivial)]
  have e2 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
    Scheme.Hom.appLE_eq_app (f := spMap φ) (U := ⊤)
  rw [e2]
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom r)) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [this]
  congr 1
  exact (Scheme.ΓSpecIso Γ(X, U.1)).inv_hom_id_apply r

theorem resG_appLE' {Y Z : Scheme.{0}} (f : Y ⟶ Z) {W : Z.Opens} {O O' : Y.Opens} (h : O' ≤ O) (e : O ≤ f ⁻¹ᵁ W)
    (a : Γ(Z, W)) : resG Y h ((f.appLE W O e).hom a) = (f.appLE W O' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

end GlobalTheory.CechKSSmul
