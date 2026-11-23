import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceFixedVectorsNeBotTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIrrGLTransportAlongFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameWeilDeligneUnderIdentityRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsThreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsFourStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RecTTransport.isRecT_transport : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → (∃ rc₀ : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc₀) → ∃ rc' : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc' ∧ ∀ x x', GlobalTheory.LocLanglands.RepRel i x x' → GlobalTheory.LocLanglands.WDRel (RingEquiv.refl Ω) (rc x) (rc' x') := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc hrc hrc₀
  obtain ⟨rc₀, a', ha', -⟩ := hrc₀
  have := FieldCompat.charZero_compl w
  have := FieldCompat.charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i P.cont).1
  obtain ⟨T, hT, -⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i P.cont
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  obtain ⟨a, ha, H⟩ := hrc
  have hR : ∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) ((fun x' => S (rc (T.symm x'))) x') :=
    fun x x' hx => (hS _ _).2 (by rw [← (hT _ _).1 hx]; exact congrArg (fun z => S (rc z)) (T.symm_apply_apply x).symm)
  have hG : ∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x') := fun x x' hx =>
    ⟨GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i P.cont x x' hx,
      GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs x' x (FieldCompat.repRel_symm hx)⟩
  obtain ⟨l1, l2, l3, l4, l5⟩ := GlobalTheory.T.place_iso_compatible_local_langlands_three E E' Ω A w w' h h' j i P rc _ hR a ha H a' ha'
  obtain ⟨m1, m2, m3, m4, m5⟩ := GlobalTheory.T.place_iso_compatible_local_langlands_four E E' Ω A w w' h h' j i P rc _ hR hG a ha H a' ha'
  refine ⟨fun x' => S (rc (T.symm x')), ⟨a', ha', ⟨l1, l2, l3, l4, l5, m1, m2, m3, m4, m5, fun x' hg hf => ?_,
    GlobalTheory.T.place_iso_compatible_local_langlands_two E E' Ω A w w' h h' j i P rc _ hR H.type⟩⟩, hR⟩
  have hx : RepRel i (T.symm x') x' := (hT _ _).2 (T.apply_symm_apply x')
  have hx' := FieldCompat.repRel_symm hx
  refine GlobalTheory.T.place_iso_compatible_local_langlands_one E E' Ω A w w' h h' j i P _ _ (hR _ _ hx) (H.depth _ ?_ ?_)
  · exact GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs _ _ hx' hg
  · exact GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport _ _ i.symm hs _ _ hx' hf

end
