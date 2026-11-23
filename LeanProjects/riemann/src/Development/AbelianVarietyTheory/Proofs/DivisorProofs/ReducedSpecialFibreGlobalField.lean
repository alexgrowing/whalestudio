import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.RedFibreField

noncomputable section

open Polynomial in

theorem exists_pow_mul_eq_zero {k R : Type} [CommRing k] [CommRing R] (hk : IsField k)
    (φ : k →+* R) (a : R) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (c b : R), IsUnit c ∧ a ^ m * (c + a * b) = 0 := by
  letI := hk.toField
  obtain ⟨p, hp, h0⟩ := ha
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hq hnd
  rw [X_dvd_iff] at hnd
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hnd).map φ, ?_⟩
  rw [hq, ← X_mul_divX_add q, eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_mul, eval₂_X,
    eval₂_C] at h0
  rw [add_comm]
  exact h0

theorem isClosed_basicOpen {Y : Scheme.{0}} {K : Type} [Field K] (p : Y ⟶ Spec (.of K))
    [UniversallyClosed p] (a : Γ(Y, ⊤)) : IsClosed (Y.basicOpen a : Set Y) := by
  have hk : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨m, c, b, hc, e⟩ :=
    exists_pow_mul_eq_zero hk _ a (isIntegral_appTop_of_universallyClosed p a)
  have : (Y.basicOpen a : Set Y) = (Y.basicOpen (c + a * b) : Set Y)ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    rw [Scheme.mem_basicOpen Y a z trivial, Scheme.mem_basicOpen Y (c + a * b) z trivial]
    let G : Γ(Y, ⊤) →+* Y.presheaf.stalk z := (Y.presheaf.germ ⊤ z trivial).hom
    change IsUnit (G a) ↔ ¬ IsUnit (G (c + a * b))
    have e' : G a ^ m * G (c + a * b) = 0 := by rw [← map_pow, ← map_mul, e, map_zero]
    constructor
    · intro h1 h2
      exact ((h1.pow m).mul h2).ne_zero e'
    · intro h2
      have hc' : IsUnit (G (c + a * b) + (- (G a * G b))) := by
        have := hc.map G
        simpa using this
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hc' with h | h
      · exact absurd h h2
      · exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h)
  rw [this]
  exact (Y.basicOpen _).isOpen.isClosed_compl

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite in
open Scheme.IdealSheafData in

theorem _root_.GlobalTheory.RedFibreField.isReduced_nilradical_subscheme (X : Scheme.{0}) : IsReduced X.nilradical.subscheme := by
  have h : X.nilradical = vanishingIdeal (⊥ : X.IdealSheafData).support := by
    rw [Scheme.nilradical, vanishingIdeal_support]
  rw [h]
  exact _root_.GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _

theorem isUnit_of_basicOpen_eq_top {Y : Scheme.{0}} (a : Γ(Y, ⊤)) (h : Y.basicOpen a = ⊤) :
    IsUnit a := by
  have key : ∀ (g : op (⊤ : Y.Opens) ⟶ op (Y.basicOpen a)) (g' : op (Y.basicOpen a) ⟶ op ⊤),
      (Y.presheaf.map g').hom ((Y.presheaf.map g).hom a) = a := by
    intro g g'
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') (𝟙 _),
      CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  have u := (Y.toRingedSpace.isUnit_res_basicOpen a).map
    (Y.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom
  convert u using 1
  exact (key _ _).symm

theorem isField_of_connected {Y : Scheme.{0}} {K : Type} [Field K] (p : Y ⟶ Spec (.of K))
    [UniversallyClosed p] [IsReduced Y] [ConnectedSpace Y] : IsField Γ(Y, ⊤) := by
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {a} ha => ?_⟩
  · have h1 : y ∈ Y.basicOpen (1 : Γ(Y, ⊤)) := by simp
    rw [← h] at h1
    simp at h1
  · have hc : IsClopen (Y.basicOpen a : Set Y) := ⟨isClosed_basicOpen p a, (Y.basicOpen a).isOpen⟩
    rcases isClopen_iff.1 hc with h | h
    · exact absurd ((AlgebraicGeometry.basicOpen_eq_bot_iff a).1 (SetLike.coe_injective (h.trans rfl))) ha
    · obtain ⟨u, hu⟩ := isUnit_of_basicOpen_eq_top a (SetLike.coe_injective (h.trans rfl))
      exact ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv⟩

end

end GlobalTheory.RedFibreField

namespace GlobalTheory.RedFibreField

theorem isField_reducedSpecialFibre : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)), IsProper f →
    ConnectedSpace (specialFibre f) → IsField Γ(reducedSpecialFibre f, ⊤) := by
  intro O _ _ _ Z f hf hc
  haveI := hf
  let Y := (specialFibre f).nilradical.subscheme
  let ι : Y ⟶ specialFibre f := (specialFibre f).nilradical.subschemeι
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
  haveI : UniversallyClosed q := by dsimp only [q]; infer_instance
  haveI : UniversallyClosed ι := by dsimp only [ι]; infer_instance
  let p : Y ⟶ Spec (.of (IsLocalRing.ResidueField O)) := ι ≫ q
  have hp : UniversallyClosed p := MorphismProperty.comp_mem @UniversallyClosed ι q ‹_› ‹_›
  haveI : IsReduced Y := isReduced_nilradical_subscheme _
  have hs : Function.Surjective ι := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.support_nilradical]
    rfl
  haveI : Nonempty Y :=
    ⟨(hs (Nonempty.some (inferInstance : Nonempty (specialFibre f)))).choose⟩
  haveI : ConnectedSpace Y := by
    refine connectedSpace_iff_univ.2 ⟨Set.univ_nonempty, ?_⟩
    refine (ι.isClosedEmbedding.isInducing.isPreconnected_image).1 ?_
    rw [Set.image_univ, hs.range_eq]
    exact isPreconnected_univ
  exact @isField_of_connected Y _ _ p hp _ _

end GlobalTheory.RedFibreField
