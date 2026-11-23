import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem SameField.basic {D D' : D7} (h : SameField D D') (h1 : SameGalois D.nd D'.nd) (h2 : TwistDataAgreeAcrossCoefficients D.ntw D'.ntw) :
    D.what₂.places.Pl = D'.what₂.places.Pl ∧ (IsGalois ℚ ↥D.LL0 → IsGalois ℚ ↥D'.LL0) ∧
    (∃ φ : ↥D.LL0 ≃+* ↥D'.LL0, ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ b x,
      HEq (sideEmb i b x) (sideEmb i' b (φ x))) ∧
    (∀ (ψ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ))
      (ψ' : D'.what₂.places.Pl → (G D'.host.E D'.nd.Om →* (D'.what₂.LL)ˣ)), HEq ψ ψ' →
      ((∀ w, ψ (D.what₂.places.conj w) = ψ w) → ∀ w, ψ' (D'.what₂.places.conj w) = ψ' w) ∧
      ∀ w w', HEq w w' → HEq (ψ w) (ψ' w') ∧ (ψ w = 1 → ψ' w' = 1)) ∧
    ∀ (w : D.what₂.places.Pl) (w' : D'.what₂.places.Pl), HEq w w' →
      HEq (D.what₂.places.conj w) (D'.what₂.places.conj w') ∧
      (∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ b, ReadsAt i b w ↔ ReadsAt i' b w') ∧
      ∀ (p : TwPack D) (p' : TwPack D'), HEq p p' → ∀ (b : Bool) (ψ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)
        (ψ' : G D'.host.E D'.nd.Om →* (D'.what₂.LL)ˣ), HEq ψ ψ' →
        (∃ ρ : Reading p.1 p.2.2.1 b w, ∀ g, ρ.emb ((ψ g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
          (algebraMap (D.ntw.Ok p.1 p.2.2.1) ρ.Oe
            ((BlochKatoReduction.Gen.psiAt b p.2.2.2 (D.ntw.art p.1 p.2.1 g) : (D.ntw.Ok p.1 p.2.2.1)ˣ) : D.ntw.Ok p.1 p.2.2.1))) →
        ∃ ρ : Reading p'.1 p'.2.2.1 b w', ∀ g, ρ.emb ((ψ' g : (D'.what₂.LL)ˣ) : D'.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
          (algebraMap (D'.ntw.Ok p'.1 p'.2.2.1) ρ.Oe
            ((BlochKatoReduction.Gen.psiAt b p'.2.2.2 (D'.ntw.art p'.1 p'.2.1 g) : (D'.ntw.Ok p'.1 p'.2.2.1)ˣ) : D'.ntw.Ok p'.1 p'.2.2.1)) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := h
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D
  cases ‹Rows.Data _›
  cases ‹NData _ _ _›
  cases ‹NTw _ _ _ _ _›
  cases D'
  cases ‹Rows.Data _›
  cases ‹NData _ _ _›
  cases ‹NTw _ _ _ _ _›
  dsimp only at a1 a2 a3 b1 b2 b3 b4 b5 b6 nOm ninstOm nalgOm nplOm nPlG xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst a1; subst a2; subst a3; subst b1; subst b2; subst b3; subst b4
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst b5; subst b6
  refine ⟨rfl, id, ⟨RingEquiv.refl _, fun i i' hi b x => ?_⟩, fun ψ ψ' hψ => ?_, fun w w' hw => ?_⟩
  · subst hi
    exact HEq.rfl
  · subst hψ
    refine ⟨id, fun w w' hw => ?_⟩
    subst hw
    exact ⟨HEq.rfl, id⟩
  · subst hw
    refine ⟨HEq.rfl, fun i i' hi b => ?_, fun p p' hp b ψ ψ' hψ => ?_⟩
    · subst hi
      exact Iff.rfl
    · subst hp
      subst hψ
      rintro ⟨ρ, hρ⟩
      exact ⟨@Reading.mk _ _ _ _ _ ρ.Oe ρ.cr ρ.dom ρ.dvr ρ.alg ρ.inj ρ.fin ρ.loc ρ.emb ρ.emb_w ρ.emb_side, hρ⟩

end GlobalTheory.TwistChoice

end
