import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonLineBundleCohomologyProjBaseChangeIfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedFieldStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.KVFromPair

theorem subsingleton_coh_twist (hN : GlobalTheory.Published.NefNumerics) (hV : GlobalTheory.Published.NadelVanishingPair)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ) [hs : SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (K : CanonLB p D) (N : LB X) (h₁ : letI := algebraΓOfHom p; IsNef k N)
    (h₂ : letI := algebraΓOfHom p; IsBig k N) (q : ℕ) (hq : 0 < q) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  have hNl : N.IsLB := by
    letI := algebraΓOfHom p
    exact h₁.isLB
  obtain ⟨K₁, X₁, p₁, ψ, L₁, hc, hp₁, H, hL₁, e⟩ := GlobalTheory.T.projectiveLineBundle_descends_to_countable_subfield k X p hp N hNl
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hg : GeometricallyConnected p := GlobalTheory.geometricallyConnected_of_isAlgClosed p
  obtain ⟨hs₁, hg₁⟩ := GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension K₁ k X₁ X p₁ p ψ H D inferInstance hs hg
  have hne : Nonempty X₁ := ⟨ψ (Classical.arbitrary X)⟩
  have hP := LB.isLB_pull hL₁ ψ
  have ec : cls N hNl = cls (L₁.pull ψ) hP := (cls_eq_iff _ _).2 e
  have n₁ := GlobalTheory.T.isNefLineBundle_of_baseChange_field K₁ k X₁ X p₁ p ψ H hp₁ L₁ hL₁ (by
    letI := algebraΓOfHom p
    exact h₁.of_cls_eq hP ec.symm)
  have b₁ := (GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff K₁ k X₁ X p₁ p ψ H hp₁ hp
    ((GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p D hs).trans
      (GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p₁ D hs₁).symm) L₁ hL₁).1 (by
    letI := algebraΓOfHom p
    exact h₂.of_cls_eq hP ec.symm)
  let C : CanonLB p₁ D := CanonLB.all p₁ D
  have v₁ := GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField hN hV K₁ (GlobalTheory.KeyHouse.nonempty_ringHom_complex K₁) X₁ p₁ D hp₁ hg₁
    C L₁ n₁ b₁ q hq
  have hT := isLB_tens C.isLB hL₁
  have v := (GlobalTheory.T.subsingleton_lineBundleCohomology_projBaseChange_iff K₁ k X₁ X p₁ p ψ H hp₁ hp _ hT q).2 v₁
  have eK : cls K.bundle K.isLB = cls (C.bundle.pull ψ) (LB.isLB_pull C.isLB ψ) := by
    obtain ⟨w, hw, -⟩ := canonLB_baseChange K₁ k _ X₁ X p₁ p ψ D H C K
    exact (cls_eq_iff _ _).2 ⟨w, hw⟩
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_tens K.isLB hNl)
    (LB.isLB_pull hT ψ) (by
      rw [cls_tens K.isLB hNl, cls_pull hT, cls_tens C.isLB hL₁, map_add, eK, ec,
        cls_pull C.isLB, cls_pull hL₁])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 v

theorem kawamataViehweg_of_nadelVanishingPair :
    GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.KawamataViehweg := by
  intro hN hV k _ _ _ X a _ D hs hp K N h₁ h₂ q hq
  have ha : a = algebraΓOfHom (strHom k X) := Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)
  have v := subsingleton_coh_twist hN hV k X (strHom k X) D hp K N (ha ▸ h₁) (ha ▸ h₂) q hq
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q (Twist.unitTwistIso _)).toEquiv.subsingleton_congr.1 v

end GlobalTheory.KVFromPair
