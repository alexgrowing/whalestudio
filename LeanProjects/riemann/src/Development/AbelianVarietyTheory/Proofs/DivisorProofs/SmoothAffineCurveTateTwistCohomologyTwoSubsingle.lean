import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNbhdKillingCurveCohomologyClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassAgreeingNearZerosStatement

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_tateTwistCohomology_two_subsingleton : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ,
    Subsingleton (Ht q (sp B) 2 i) := by
  intro q _ k B _ _ _ _ _ _ hq i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)).ne'
  have hζ : ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨algebraMap k B z, ?_⟩
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic,
      hz.eq_zero, map_zero]
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q B hqB hζ 2 i 1
  have h0 : ∀ x : Ht q (sp B) 2 1, x = 0 := by
    intro x
    obtain ⟨f, hf, hxf⟩ := GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two q k B hq 1 x
    obtain ⟨A', _, _, hA', hxA'⟩ := GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass q k B hq f hf 2 1 (by norm_num) x
    obtain ⟨w, hw⟩ := GlobalTheory.T.etaleExcision_vanishing_under_refinement q B A' f hA' 1 1 x hxf hxA'
    obtain ⟨g, hfg, A₂, C, _, _, _, _, _, _, h2, hg, hC, a, haC, hwa⟩ := GlobalTheory.T.exists_kummerClass_agreeing_near_zeros q k B hq f hf A' hA' w
    exact hw g hfg A₂ C h2 hg hC a haC hwa
  exact ⟨fun a b => e.injective (by rw [h0 (e a), h0 (e b)])⟩

end GlobalTheory.EtC
