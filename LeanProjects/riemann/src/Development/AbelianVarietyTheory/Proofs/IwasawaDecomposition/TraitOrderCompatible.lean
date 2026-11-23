import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedOfHeightOneLocalizationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeigStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkLocalizationEqGenerizationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionDvrInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointInOpenOfInjectiveStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef.Overlap

theorem isDiscreteValuationRing_of_ringEquiv {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (e : A ≃+* B) (h : IsDiscreteValuationRing A) : IsDiscreteValuationRing B := by
  have : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : IsLocalRing B := IsLocalRing.of_surjective' e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  rw [Ne, ← IsLocalRing.isField_iff_maximalIdeal_eq]
  intro hF
  exact IsDiscreteValuationRing.not_isField A (MulEquiv.isField hF e.toMulEquiv)

theorem associated_of_dvr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c)
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)) (hC : HasCones Cn Z) (U U' : Z.X.Opens)
    (f : Γ(Z.X, U)) (f' : Γ(Z.X, U')) (ho : TraitOrd φ Z U f) (ho' : TraitOrd φ Z U' f') (y : Z.X) (hy : y ∈ U)
    (hy' : y ∈ U') [IsDomain (Z.X.presheaf.stalk y)] (hd : IsDiscreteValuationRing (Z.X.presheaf.stalk y)) :
    Associated ((Z.X.presheaf.germ U y hy).hom f) ((Z.X.presheaf.germ U' y hy').hom f') := by
  obtain ⟨R, _, _, _, ξ, t, m, P, k, γ, hcn, hξ, het, -, -, -, -⟩ := hC y
  subst hξ
  obtain ⟨hR, hinj, hdesc⟩ := GlobalTheory.T.etale_completion_dvr_injective _ R _ hcn het
  have hR' := hR
  obtain ⟨hdvrR, hcpl, hch0⟩ := hR'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨be, hbe, hmon, -⟩ := exists_periodForm P hϖ
  have hr := GlobalTheory.T.generic_point_in_open_of_injective Z R ξ hinj
  obtain ⟨n, hn, h1⟩ := ho R hR ϖ hϖ ξ t m P hr be hbe hmon hy
  obtain ⟨n', hn', h2⟩ := ho' R hR ϖ hϖ ξ t m P hr be hbe hmon hy'
  have e : n = n' := by exact_mod_cast hn.trans hn'.symm
  subst e
  exact hdesc _ _ (h1.trans h2.symm)

theorem isLocallyNoetherian_gmod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) : IsLocallyNoetherian Z.X := by
  obtain ⟨-, hft, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  have : IsNoetherianRing (𝓞 c.F) := Algebra.FiniteType.isNoetherianRing ℤ (𝓞 c.F)
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  exact LocallyOfFiniteType.isLocallyNoetherian Z.s

theorem associated_germ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → ∀ (U U' : Z.X.Opens) (f : Γ(Z.X, U)) (f' : Γ(Z.X, U')), IsRegularFn f → IsRegularFn f' → TraitOrd φ Z U f → TraitOrd φ Z U' f' → ∀ (x : Z.X) (hx : x ∈ U) (hx' : x ∈ U'), Associated ((Z.X.presheaf.germ U x hx).hom f) ((Z.X.presheaf.germ U' x hx').hom f') := by
  intro E _ _ _ H D l Xo c Z Cn φ hC U U' f f' hf hf' ho ho' x hx hx'
  have := isLocallyNoetherian_gmod Z
  obtain ⟨hdx, hicx⟩ := Z.normal x
  have ha := nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 hf x hx)
  have hb := nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 hf' x hx')
  refine GlobalTheory.T.associated_of_height_one_localizations _ _ _ ha hb fun q _ hq => ?_
  obtain ⟨y, h, e, he⟩ := GlobalTheory.T.stalk_localization_eq_generization Z.X x q
  have hy : y ∈ U := h.mem_open U.isOpen hx
  have hy' : y ∈ U' := h.mem_open U'.isOpen hx'
  obtain ⟨hdy, -⟩ := Z.normal y
  have hd : IsDiscreteValuationRing (Z.X.presheaf.stalk y) :=
    isDiscreteValuationRing_of_ringEquiv e (GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' _ q hq)
  have key := associated_of_dvr Z Cn φ hC U U' f f' ho ho' y hy hy' hd
  have g1 : (Z.X.presheaf.germ U y hy).hom f = e (algebraMap _ _ ((Z.X.presheaf.germ U x hx).hom f)) := by
    rw [he, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have g2 : (Z.X.presheaf.germ U' y hy').hom f' = e (algebraMap _ _ ((Z.X.presheaf.germ U' x hx').hom f')) := by
    rw [he, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [g1, g2] at key
  simpa using key.map e.symm

end GlobalTheory.TorRef.Overlap
