import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateFunctionalsFunctionFieldExtensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTraceCoefficientsNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowAmpleForallLocalConditionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackLeMulTwistDominantStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GlobalSectionsPullback

theorem globalSectionsDim_pullback_le_generically_finite : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (p : W ⟶ Sp F) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → Surjective f →
    f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (A : LB W), IsAmpleLB A ∧
      ∀ B : LB W, B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤
        r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  intro F _ M W _ _ p f hp hfp _ hdeg
  obtain ⟨r, co, hco, hinj⟩ := GlobalTheory.T.exists_coordinateFunctionals_functionField_extension M W f hdeg
  obtain ⟨hpp, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨hfpp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (f ≫ p)).1 hfp
  haveI := hpp
  haveI := hfpp
  haveI : IsProper f := IsProper.of_comp f p
  haveI : IsNoetherian W := isNoetherian_of_isProjOver hp
  obtain ⟨n, hn, t, ht, htP⟩ := GlobalTheory.T.exists_section_pow_ample_forall_local_condition W H hH
    (fun y c => ∀ (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V')
      (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (c * co j (fnOf (f ⁻¹ᵁ V') h z)))
    (fun y c c' hc hc' V' hy h z j => by rw [mul_assoc]; exact hc'.mul (hc V' hy h z j))
    (fun y => by
      obtain ⟨V, hy, d, hd, hd'⟩ := GlobalTheory.T.exists_open_trace_coefficients_nonvanishing M W f L hL co hco y
      exact ⟨V, hy, d, hd, fun y' hy' V' hV' h z j => hd' y' hy' V' hV' h z j⟩)
  exact ⟨r, lbPow H n, (isAmpleLB_pow_iff hH.isLB hn).2 hH, fun B hB =>
    GlobalTheory.T.finrank_sections_pullback_le_mul_twist_of_dominant F M W p f hp co hco hinj (lbPow H n) (isLB_lbPow hH.isLB n) t ht
      (fun y i hi V' hV' h z j => htP y i hi V' hV' h z j) B hB⟩

end GlobalTheory.GlobalSectionsPullback
