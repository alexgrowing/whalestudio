import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePartStatement

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertSuppChar

theorem eq_one_at_inert {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (μ : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* Circle)
    (hμ : ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → μ k = 1)
    {q : ℕ} (hq : q.Prime) (hi : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) :
    μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 := by
  obtain ⟨g, hg⟩ := GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG y rfl
  rw [← GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hg]
  obtain ⟨l, hl, e⟩ := GlobalTheory.T.exists_prod_localComponents_eq_primePart V hG q hq g
  rw [← e, map_list_prod, map_list_prod, List.map_map]
  refine List.prod_eq_one (M := Circle) fun z hz => ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hz
  obtain ⟨v, ε, hε, hqv, hs⟩ := hl h hh
  have hn : GlobalTheory.WeilParts.NonSplitAt D v ε := (GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq v ε hε hqv).1 hi
  refine GlobalTheory.InertChar.char_eq_one_of_nonSplit D V _
    (GlobalTheory.NormRatio.SphCoset.isSelfDualC_of_gram_one hG (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D V.rank)) v ε hn
    (μ.comp (GlobalTheory.BotClassDict.finStd V hG)) (fun k hk hst => ?_) h hs
  obtain ⟨a1, a2⟩ := GlobalTheory.T.nonSplitSupported_finitePart_integral_inert V hG v ε hn k hk hst
  exact hμ _ a1 a2

theorem char_eq_one : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D), V.gram = 1 → ∀ (ν : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* ℂˣ),
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
    Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  ∀ x, ν x = 1 := by
  intro D V hG ν hs hi x
  refine GlobalTheory.T.eq_one_of_forall_circle_char_eq_one ν x fun μ hμ => ?_
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun q => ¬ Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x, map_mul,
    hμ _ (hs _ (GlobalTheory.NormSum.VacInt.suppSplit_part D x)), one_mul]
  have hy := GlobalTheory.NormSum.VacInt.suppInert_part D x
  generalize GlobalTheory.NormSum.VacInt.part D (fun q => ¬¬Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x = y at hy ⊢
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite y hy
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun p => p ∈ s) y, map_mul,
    hμ _ (hi _ (GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes _ _ hy) hs2), mul_one]
  have hloc : ∀ q, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 :=
    fun q hq hqi => eq_one_at_inert V hG μ (fun k a1 a2 => hμ _ (hi k a1 a2)) hq hqi y
  clear hs2
  induction s using Finset.induction_on with
  | empty => rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).1, map_one]
  | insert q s hq ih =>
    rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).2 q s hq, map_mul, hloc q (hs1 q (Finset.mem_insert_self q s)).1
      (hs1 q (Finset.mem_insert_self q s)).2, one_mul]
    exact ih fun p hp => hs1 p (Finset.mem_insert_of_mem hp)

end GlobalTheory.InertSuppChar
