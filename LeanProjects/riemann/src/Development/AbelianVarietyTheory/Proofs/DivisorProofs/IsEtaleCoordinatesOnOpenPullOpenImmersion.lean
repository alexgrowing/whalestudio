import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem isEtCoord_openImmersion (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X)
    [IsOpenImmersion e] (U : X.Opens) (W : Y.Opens) (h : W ≤ e ⁻¹ᵁ U) (d : ℕ) (t : Fin d → Γ(X, U)) :
    IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t →
      IsEtCoord (e ≫ f) W (fun a => (e.appLE U W h).hom (t a)) := by
  intro hU hW ht
  have hφ : (e.appLE U W h).hom.Etale := e.etale_appLE hU hW h
  have hc : (e.appLE U W h).hom.comp (cstOn f U) = cstOn (e ≫ f) W := by
    have e₁ : f.appLE ⊤ U le_top ≫ e.appLE U W h = (e ≫ f).appLE ⊤ W le_top :=
      Scheme.Hom.appLE_comp_appLE e f ⊤ U W le_top h
    have e₂ : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) ≫ e.appLE U W h =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (e ≫ f).appLE ⊤ W le_top := by
      rw [Category.assoc, e₁]
    exact congrArg CommRingCat.Hom.hom e₂
  unfold IsEtCoord
  rw [← hc, ← MvPolynomial.comp_eval₂Hom]
  exact RingHom.Etale.stableUnderComposition _ _ ht hφ

end GlobalTheory.LogPair
