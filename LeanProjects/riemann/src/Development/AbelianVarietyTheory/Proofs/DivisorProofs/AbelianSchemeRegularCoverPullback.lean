import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyThetaAfterExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverOverFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackCompositeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackCancelLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackCancelRightStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.ThetaCover

theorem exists_regCover_hasTheta : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k]
    (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ P : PPAS X,
    ∃ (C : RegCover p) (P' : PPAS C.Y) (φ : P'.A.left ⟶ P.A.left), P'.IsPull P C.ρ φ ∧ P'.g = P.g ∧ P'.HasTheta := by
  intro _ hRA k _ X p _ hX P
  obtain ⟨Pη, φη, -, hPη⟩ := PPAS.exists_pull X (Sp X.functionField) P (X.fromSpecStalk (genericPoint X))
  obtain ⟨F, _, _, hfin, hF⟩ := GlobalTheory.T.abelian_variety_theta_after_extension X.functionField Pη
  obtain ⟨C, t, ht⟩ := GlobalTheory.T.regular_cover_over_finite_extension hRA k X p hX F hfin
  obtain ⟨P', φ, hg, hP⟩ := PPAS.exists_pull X C.Y P C.ρ
  have h1 := GlobalTheory.T.theta_pullback_cancel_right _ _ _ P Pη _ φη _ hPη hF
  have h2 := GlobalTheory.T.theta_pullback_composite _ _ _ P _ t h1
  rw [ht] at h2
  have h3 := GlobalTheory.T.theta_pullback_cancel_left _ _ _ P P' C.ρ φ _ hP h2
  exact ⟨C, P', φ, hP, hg, GlobalTheory.T.theta_descends_from_generic_fibre k C.Y (C.ρ ≫ p) C.reg P' h3⟩

end GlobalTheory.ThetaCover

end
