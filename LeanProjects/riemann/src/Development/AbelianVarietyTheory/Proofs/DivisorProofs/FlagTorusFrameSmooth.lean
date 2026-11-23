import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameWeylPermutationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointLiftValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

theorem Lands.residue_of_fraction : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp) (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (ψ : Γ(gen Z, V) →+* R) (a : Cell.Coord Dw → R), Cell.Lands Φ hV f₀ w i ((algebraMap R K).comp ψ) (algebraMap R K ∘ a) → Cell.Lands Φ hV f₀ w i ((IsLocalRing.residue R).comp ψ) (IsLocalRing.residue R ∘ a) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ V hV φV f₀ w i R _ _ _ K _ _ _ ψ a h
  have hc : ∀ {S : Type} [CommRing S] (ν : R →+* S), spMap (ν.comp ψ) = spMap ν ≫ spMap ψ := fun ν => by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨gL, hgL, pL, hpL, hcL⟩ := h
  obtain ⟨q, hq, hqL⟩ := GlobalTheory.FlagCptLift.exists_lift E H Dw l Xo c O β Z F e (Φ.C i) R K
    (spMap ψ ≫ hV.fromSpec) pL (by rw [hpL, hc, Category.assoc])
  obtain ⟨gV, hgV⟩ := exists_frameIn hV f₀ w ψ rfl a
  obtain ⟨gk, hgk⟩ := exists_frameIn hV f₀ w ((IsLocalRing.residue R).comp ψ) rfl (IsLocalRing.residue R ∘ a)
  obtain ⟨tL, htL⟩ := GlobalTheory.T.eigen_frame_weyl_permutation hV f₀ w (algebraMap R K) ψ rfl rfl gV gL a hgV hgL
  obtain ⟨tk, htk⟩ := GlobalTheory.T.eigen_frame_weyl_permutation hV f₀ w (IsLocalRing.residue R) ψ rfl rfl gV gk a hgV hgk
  refine ⟨gk, hgk, spMap (IsLocalRing.residue R) ≫ q, by rw [Category.assoc, hq, hc, Category.assoc], ?_⟩
  exact GlobalTheory.CarrySpec.carries_spec E H Dw l Xo c O β Z F e (Φ.C i) R K (algebraMap R K)
    (IsFractionRing.injective R K) _ (IsLocalRing.residue R) IsLocalRing.ker_residue q _ _
    (by rw [← hq, Category.assoc]) gV _ _ gL tL htL (hqL ▸ hcL) _ _ gk tk htk

end GlobalTheory.ShFam.Cell
