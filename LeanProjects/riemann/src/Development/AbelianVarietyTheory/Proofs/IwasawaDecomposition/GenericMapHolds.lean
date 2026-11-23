import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointOfFlatLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOfRefinedFanStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenMap

theorem gen_factor : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j], Dense (Set.range j) →
    (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X),
    (Scheme.stalkClosedPointTo ξ).hom.Flat → ∃ y : Sp (FractionRing R) ⟶ U, y ≫ j = jK R ≫ ξ := GlobalTheory.T.generic_point_of_flat_local

theorem chart_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ)
    (φ : InvFun (𝓞 E)) (d k : ℕ) (DX : GlobalTheory.EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    Refines H (min D.p D.q) φs 𝒩 φ → IsPol (comb d (resInt _ φs) 0 φ) k X DX →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (mξ : SABMap t Y.t ξ)
      (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
      IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
      ConeO H φ P.D.toPre.X m γ → InCone P.D.toPre γ →
      ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ → ∃ χ : Sp R ⟶ X.X, jK R ≫ χ = y ≫ X.j := GlobalTheory.T.polarization_of_refined_fan

theorem isIso_spMap_id (F : Type) [Field F] : IsIso (spMap (RingHom.id F)) := by
  simp only [spMap, CommRingCat.ofHom_id]
  infer_instance

theorem isOpenImmersion_j {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  have := isIso_spMap_id c.F
  have := Y.jQ_open
  unfold Model.j
  infer_instance

theorem hom_ext_jK {R : Type} [CommRing R] [IsDomain R] {Z : Scheme.{0}} [Z.IsSeparated] {f g : Sp R ⟶ Z}
    (h : jK R ≫ f = jK R ≫ g) : f = g := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le)⟩
  exact ext_of_isDominant (jK R) h

theorem genMapSt : GenMapSt := by
  intro E _ _ _ H D l Xo c X Y g φs 𝒩 φ d k DX hg hfan href hpol hcone
  have hidY : IsDedFrac (RingHom.id c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩
  obtain ⟨hYn, hYr, hYs, -, -, hYd, -⟩ := GlobalTheory.ModelRelCompare.densePart Y hidY
  obtain ⟨-, -, hXs, -, -, -, -⟩ := GlobalTheory.ModelRelCompare.densePart X (GlobalTheory.ModelRelCompare.isDedFrac_in_use c).1
  have hYj := isOpenImmersion_j Y
  have hXp := isProper_toroidalModel_structureMap X
  have hw : X.j ≫ X.s = Y.j ≫ Y.s ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    simp only [Model.j, Category.assoc, pullback.condition, pullback.condition_assoc]
    rw [← Category.assoc X.jQ, X.jQ_over, ← Category.assoc Y.jQ, Y.jQ_over]
    simp [spMap, CommRingCat.ofHom_id]
  have hext : ∀ z : Y.X, ExtAt Y.j X.j (𝟙 Y.X) z := by
    intro z
    obtain ⟨R, _, _, _, ξ, t, mξ, P, m, γ, hR, hz, hE, hU, hT, hC, hI⟩ := hcone z
    obtain ⟨y, hy⟩ := gen_factor Y.X (Xo.XF c) Y.j hYd.denseRange (fun x => (Y.normal x).1) R ξ hE.1
    obtain ⟨χ, hχ⟩ := chart_extends E H D l Xo c X Y g φs 𝒩 φ d k DX hg hfan href hpol R ξ t mξ P m γ hR hE hU hT hC hI y hy
    have hχs : χ ≫ X.s = ξ ≫ 𝟙 Y.X ≫ Y.s ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      refine hom_ext_jK ?_
      rw [reassoc_of% hχ, hw, Category.id_comp, ← reassoc_of% hy]
    rw [← hz]
    exact GlobalTheory.ExtAtProof.extAtSt Y.X Y.X (Xo.XF c) X.X (Sp (𝓞 c.F)) (𝟙 Y.X) Y.j X.j
      (Y.s ≫ spMap (algebraMap (𝓞 c.F) c.F)) X.s R ξ y χ inferInstance inferInstance inferInstance hw hE.1
      (by rw [Category.comp_id, hy]) hχ hχs
  obtain ⟨h, hh⟩ := GlobalTheory.TorRef.glueSt Y.X Y.X (Xo.XF c) X.X (𝟙 Y.X) Y.j X.j hYr hYj (by have hD : Dense (Set.range Y.j) := hYd.denseRange; simpa using hD) hXs hext
  have hj : Y.j ≫ h = X.j := by simpa using hh (Xo.XF c) Y.j (𝟙 _) (by simp)
  have := isIso_spMap_id c.F
  have hgr : IsReduced (gen Y) := isReduced_of_isOpenImmersion (genι Y)
  have hdom : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := by simp [spMap, CommRingCat.ofHom_id]
  have hw2 : (genι Y ≫ h) ≫ X.s = genStr Y ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    refine ext_of_isDominant Y.jQ ?_
    have e1 : Y.jQ ≫ genι Y ≫ h = X.j := hj
    rw [Category.assoc, reassoc_of% e1, hw]
    simp only [Model.j, genStr, Category.assoc, pullback.condition_assoc, hid, Category.id_comp]
  refine ⟨pullback.lift (genι Y ≫ h) (genStr Y) hw2, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact hj
  · simp only [Category.assoc, pullback.lift_snd]
    exact Y.jQ_over.trans X.jQ_over.symm

end GlobalTheory.GenMap
