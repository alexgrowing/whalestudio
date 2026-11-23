import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.LocalRingGeneralisation

theorem stalk_fromSpecStalk_equiv (X : Scheme.{0}) (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))) ≃+*
        Localization.AtPrime p,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈ U)
        (hx : x ∈ U) (s : Γ(X, U)),
        e ((X.presheaf.germ U _ hq).hom s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  rw [← h2]
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

theorem exists_generisation_height_one : ∀ (X : Scheme.{0}) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) (q : Ideal (X.presheaf.stalk (ξ (closedPoint R)))) [q.IsPrime], q.height = 1 → ∃ (z : X) (hs : z ⤳ ξ (closedPoint R)), ringKrullDim (X.presheaf.stalk z) = 1 ∧ q.map (X.presheaf.stalkSpecializes hs).hom = maximalIdeal (X.presheaf.stalk z) ∧ ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), (maximalIdeal W).comap (g.comp (Scheme.stalkClosedPointTo ξ).hom) = q → (spMap g ≫ ξ) (closedPoint W) = z := by
  intro X R _ _ ξ q _ hq
  let y : PrimeSpectrum (X.presheaf.stalk (ξ (closedPoint R))) := ⟨q, inferInstance⟩
  obtain ⟨e, he⟩ := stalk_fromSpecStalk_equiv X (ξ (closedPoint R)) q
  have hs : X.fromSpecStalk (ξ (closedPoint R)) y ⤳ ξ (closedPoint R) := by
    have : X.fromSpecStalk (ξ (closedPoint R)) y ∈ Set.range (X.fromSpecStalk (ξ (closedPoint R))) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hcomp : X.presheaf.stalkSpecializes hs ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk (ξ (closedPoint R))) (Localization.AtPrime q)) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    change e ((X.presheaf.stalkSpecializes hs).hom ((X.presheaf.germ U _ hxU).hom s)) =
      algebraMap _ (Localization.AtPrime q) ((X.presheaf.germ U _ hxU).hom s)
    rw [h3]
    exact he U _ hxU s
  have hf : (X.presheaf.stalkSpecializes hs).hom = e.symm.toRingHom.comp (algebraMap _ (Localization.AtPrime q)) := by
    ext a
    have h5 : e ((X.presheaf.stalkSpecializes hs).hom a) =
        algebraMap _ (Localization.AtPrime q) a := congrArg (fun f => f.hom a) hcomp
    change _ = e.symm (algebraMap _ (Localization.AtPrime q) a)
    rw [← h5, e.symm_apply_apply]
  refine ⟨X.fromSpecStalk (ξ (closedPoint R)) y, hs, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  · rw [hf, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    have : (Ideal.map e.symm.toRingHom (maximalIdeal (Localization.AtPrime q))).IsMaximal :=
      Ideal.map_isMaximal_of_equiv e.symm
    exact IsLocalRing.eq_maximalIdeal this
  · intro W _ _ g hg
    have h4 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have h6 : (Spec.map (Scheme.stalkClosedPointTo ξ)) ((spMap g) (closedPoint W)) = y := by
      apply PrimeSpectrum.ext
      change _ = q
      rw [← hg]
      rfl
    have h7 : (spMap g ≫ ξ) (closedPoint W) = X.fromSpecStalk (ξ (closedPoint R))
        ((Spec.map (Scheme.stalkClosedPointTo ξ)) ((spMap g) (closedPoint W))) := by
      conv_lhs => rw [← h4]
      rfl
    rw [h7, h6]

end GlobalTheory.LocalRingGeneralisation
