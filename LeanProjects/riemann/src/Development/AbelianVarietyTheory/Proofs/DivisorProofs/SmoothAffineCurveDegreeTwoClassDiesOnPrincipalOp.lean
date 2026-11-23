import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFuncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekindStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomainStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_degreeTwo_class_dies_on_principalOpen : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) →
    ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧
      pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq i x
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · have hSH : SH B := GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB
    haveI : Subsingleton (Ht q (sp B) 2 i) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B hSH (tw q i) 2 (by norm_num)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Subsingleton.elim x 0, map_zero]
  · obtain ⟨inst, halg⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    letI := inst
    haveI := halg
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    haveI : Subsingleton (Ht q (sp (FractionRing B)) 2 i) :=
      GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK 2 i le_rfl
    obtain ⟨f, hf, -, hx⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB 2 i x (Subsingleton.elim _ _)
    exact ⟨f, hf, hx⟩

end GlobalTheory.EtC
